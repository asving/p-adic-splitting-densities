/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG59

/-!
# Uniformity.ChapI.IFCG66 — [LSF 2026-08-31] the sub-face leaf census: the frame
partition, the per-frame laws, and the masters re-based

Stage LSF of the cone census (design record `runs/wave-c/verdict_LSF.md`; consumes
TBT = `IFCG59` and, through it, LSC = `IFCG57` and the whole spine).  TBT's
discharge pointer: the sub-face leaf cells FIBER over (the face data `(h, e', d)`)
× (the residual cofactor's smaller-mass class data), with the block's type pinned
`⟨{(e', d)}⟩` and `σ.data = (e', d) ::ₘ (typeOf R).data`.  This file lands the
census-side consequences of that pin:

* **§1 THE EXTENDED PINNED TRANSPORT** (`subface_transport_pinned`): TBT's
  `subface_two_block_transport` re-run with two NEW outputs — (i) the face's
  residual degree is the CLASS residual's degree,
  `(classResidualPoly π c h e').natDegree = d` (so the frame `(h, e', d)` is a
  lift-free function of the cell), and (ii) THE STEEPNESS SEED:
  `sideSet X R h e' = {R.natDegree}` — the cofactor's `(h, e')`-side touches ONLY
  its monic point, i.e. every proper abscissa of `R` sits STRICTLY above the face
  line (the disjoint-slope separation, lift-side exact).  The coefficient forms:
  `strict_cone_of_side_singleton` (lift-side, `ℕ∞`) and
  `class_strict_cone_of_side_singleton` (class-side, windowed `resOrd`), composed
  into ★ `subface_cofactor_class` — the fibering's forward half: cell ↦ (pinned
  face block, steep smaller-mass cofactor class).
* **§2 THE FRAME PARTITION**: `subFrames m σ` (the finitely many admissible
  `(h, e', d)`: `1 ≤ h < e'` coprime, `1 ≤ d`, `e'·d < m`, `(e', d) ∈ σ.data`) and
  the exact level-wise partition `leafSubSector = ⋃_{frames} subfaceCell` with the
  count identity `leafSubCount = Σ_{frames} #subfaceCell`.
* **§3 THE PER-FRAME LAWS**: `SubfaceFrameLaw m h e' d σ` (the `ZcURLim` of the
  normalized per-frame count) and ★ `leafSubfaceLaw_of_frameLaws`:
  `LeafSubfaceLaw m σ` from the finitely many per-frame laws.
* **§4 THE MASTERS RECOMPUTED**: all three spines' leaf rows re-based from the
  joint `LeafSubfaceLaw e σ` to the per-frame `SubfaceFrameLaw` family (singleton
  σ stays closed by TBT; the guards are unchanged).

## Honest scope

NOT proved here (the exact remainder after this file): the per-frame law
`SubfaceFrameLaw m h e' d σ` itself — the face digit box (LSC's necklace count at
mass `e'·d`) convolved with the STEEP mass-`(m − e'·d)` cofactor census through
the pinned-depth `q^{h·d·(m−e'·d)}` fiber clusters (CSL/RDC's engines).  Nothing
weakened: `LeafSubfaceLaw`/`LeafSectorLaw`/the master statements are byte-untouched
upstream; the new masters STRENGTHEN the landed ones (their premise families are
implied by the landed rows' premises via `leafSubfaceLaw_of_frameLaws`).

## Axiom fence (machine-exact at landing)

§1–§3 inherit Lean core `{propext, Classical.choice, Quot.sound}` + EXACTLY the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42, through IFCG59's split engine — never re-consumed); the §4 spine wrappers
additionally inherit `agnprw_termination` (ID12's, previously declared) on the
capstone form.  The C.33 cites and `AX_cellRecursion` must NOT occur.  Zero
sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG66

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_sum ConeRemainderLaw)
open Uniformity.Density.IFCG23 (le_npHgt_monicPoly npHgt_monicPoly_eq
  npHgt_monicPoly_top)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains
  exists_pure_factor_of_two_point_side mem_sideSet_of_onSide)
open Uniformity.Density.IFCG17 (monicPoly_coeff_eq_self)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_unique minFaceAt_support
  classResidualPoly classResidualPoly_eq leafSector LeafSectorLaw)
open Uniformity.Density.IFCG57 (leafSubSector leafSubCount LeafSubfaceLaw
  leafSectorLaw_of_subface)
open Uniformity.Density.IFCG59 (subface_two_block_split leafSubfaceLaw_of_card_le_one)

attribute [local instance] Classical.propDecidable

/-! ## §0 — kit (private replicas of the established supply) -/

section Kit

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

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

/-- The monic top point (private copy of IFCG59's). -/
private theorem npHgt_monic_top {g : Polynomial O} (hg : g.Monic) :
    npHgt X g g.natDegree = 0 := by
  rw [npHgt_X, hg.coeff_natDegree]
  exact IsDiscreteValuationRing.addVal_one

/-- The monic point caps the support value (private copy of IFCG59's). -/
private theorem suppVal_ne_top_of_monic {g : Polynomial O} (hg : g.Monic) (u ℓ : ℕ) :
    suppVal X g u ℓ ≠ ⊤ := by
  have hle : suppVal X g u ℓ ≤ ℓ • npHgt X g g.natDegree + ((u * g.natDegree : ℕ) : ℕ∞) := by
    rw [suppVal]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  rw [npHgt_monic_top hg, smul_zero, zero_add] at hle
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle

private theorem resPoly_congr {π : O} {u ℓ : ℕ} {f₁ f₂ : Polynomial O} (hf : f₁ = f₂)
    (hn1 : (sideSet X f₁ u ℓ).Nonempty) (hn2 : (sideSet X f₂ u ℓ).Nonempty) (H : ℕ) :
    resPoly π X f₁ u ℓ hn1 H = resPoly π X f₂ u ℓ hn2 H := by
  subst hf
  rfl

private theorem sideMin_congr {u ℓ : ℕ} {f₁ f₂ : Polynomial O} (hf : f₁ = f₂)
    (hn1 : (sideSet X f₁ u ℓ).Nonempty) (hn2 : (sideSet X f₂ u ℓ).Nonempty) :
    sideMin X f₁ u ℓ hn1 = sideMin X f₂ u ℓ hn2 := by
  subst hf
  rfl

private theorem sideDeg_congr {u ℓ : ℕ} {f₁ f₂ : Polynomial O} (hf : f₁ = f₂)
    (hn1 : (sideSet X f₁ u ℓ).Nonempty) (hn2 : (sideSet X f₂ u ℓ).Nonempty) :
    sideDeg X f₁ u ℓ hn1 = sideDeg X f₂ u ℓ hn2 := by
  subst hf
  rfl

/-- Exact disjoint-union count over a finite index set (IFCG51's private replica). -/
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

end Kit

/-! ## §1 — ★★ THE EXTENDED PINNED TRANSPORT: TBT's pin PLUS the class-residual
degree read and the cofactor steepness seed -/

section Transport

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **THE EXTENDED PINNED TRANSPORT** (TBT's `subface_two_block_transport` with
two new outputs): every lift of a sub-face leaf cell at the minimal face `(h, e')`
splits as `monicPoly a = g · R` with the block's type PINNED (`typeOf g =
⟨{(e', d)}⟩`, `g.natDegree = e' * d`, `e' * d < m`,
`σ.data = (e', d) ::ₘ (typeOf R).data`) — AND

* `(classResidualPoly π c h e').natDegree = d`: the frame datum `d` is read off
  the CLASS (lift-free), so `(h, e', d)` indexes the cells canonically;
* `sideSet X R h e' = {R.natDegree}`: the cofactor's `(h, e')`-side is the single
  monic point — every abscissa `j < deg R` of `R` sits STRICTLY above the face
  line (the disjoint-slope separation seed).

Mechanism: IFCG59 §3's proof verbatim (B.39a §7's product side laws + the
irreducibility unit argument + IFCG37's `residualLeafLaw_all`), extended at the
end: `natDegree_resPoly` reads the class residual's degree as `sideDeg` of the
lift, which the product law pins to `d + 0`; the face's right endpoint `m` is
on-side (`NPAttains c h e' m` from the minimal face), so `sideMax = m`, hence
`sideMin R = m − e'·d = deg R` and the cofactor's side collapses to its monic
point. -/
theorem subface_transport_pinned {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ leafSubSector O π m σ M) {h e' : ℕ} (hF : MinFaceAt c h e')
    {a : Fin m → O} (ha : proj O m (M + m) a = c) :
    ∃ (g R : Polynomial O) (d : ℕ), monicPoly a = g * R ∧ g.Monic ∧ R.Monic
      ∧ IsPure X g h e' ∧ 0 < d ∧ g.natDegree = e' * d ∧ e' * d < m
      ∧ typeOf g = ⟨{(e', d)}⟩ ∧ R.natDegree = m - e' * d
      ∧ σ.data = (e', d) ::ₘ (typeOf R).data
      ∧ (classResidualPoly π c h e').natDegree = d
      ∧ sideSet X R h e' = {R.natDegree} := by
  -- the carrier data at the INPUT face (unique minimal face)
  obtain ⟨hcar, h₃, e₃, hF₃, hirr₃, hnA0₃⟩ := hc
  obtain ⟨hh3, he3⟩ := minFaceAt_unique hF hF₃
  subst hh3
  subst he3
  have hstr := hcar.1.1.2
  have hh1 : 1 ≤ h := hF.1
  have hhe : h < e' := hF.2.1
  have hcop : Nat.Coprime h e' := hF.2.2.1
  have hvis : NPVisibleAt c h e' := hF.2.2.2.2.2
  have hAm : NPAttains c h e' m := hF.2.2.2.2.1
  have he'0 : 0 < e' := by omega
  have hh0 : 0 < h := by omega
  -- IFCG59 §1's split, aligned to the input face by uniqueness
  obtain ⟨g, R, hgm, hRm, heq, hgd, hRd, ⟨h₂, e₂, hF₂, hgpure₂⟩, hdata⟩ :=
    subface_two_block_split hπ hm0 ⟨hcar, h, e', hF, hirr₃, hnA0₃⟩ ha
  obtain ⟨hh2, he2⟩ := minFaceAt_unique hF hF₂
  subst hh2
  subst he2
  have hgpure : IsPure X g h e' := hgpure₂
  -- the block's side data: the pure side spans `[0, deg g]`
  have hOg0 : OnSide X g h e' 0 := hgpure.1
  have hOgtop : OnSide X g h e' g.natDegree := by
    have h2 := hgpure.2
    rwa [Polynomial.natDegree_X, Nat.div_one] at h2
  have h0memg : 0 ∈ sideSet X g h e' := mem_sideSet_of_onSide (Nat.zero_le _) hOg0
  have hdmemg : g.natDegree ∈ sideSet X g h e' := mem_sideSet_of_onSide le_rfl hOgtop
  have hnf : (sideSet X g h e').Nonempty := ⟨0, h0memg⟩
  have hming : sideMin X g h e' hnf = 0 :=
    Nat.le_zero.mp (Finset.min'_le _ 0 h0memg)
  have hmaxg : sideMax X g h e' hnf = g.natDegree := by
    refine le_antisymm ?_ (Finset.le_max' _ _ hdmemg)
    refine Finset.max'_le _ _ _ ?_
    intro y hy
    have := (mem_sideSet_iff'.mp hy).1
    omega
  have htg : suppVal X g h e' ≠ ⊤ := suppVal_ne_top_of_monic hgm h e'
  -- the block's side degree `d`: `deg g = e' * d`
  have hsdg : g.natDegree = e' * sideDeg X g h e' hnf := by
    have h5 := sideMax_eq he'0 hcop htg hnf
    rwa [hmaxg, hming, zero_add] at h5
  set d := sideDeg X g h e' hnf with hd_def
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h1
    · rw [h0, Nat.mul_zero] at hsdg
      omega
    · exact h1
  -- the left heights, named
  have hHgne : npHgt X g (sideMin X g h e' hnf) ≠ ⊤ :=
    npHgt_ne_top_of_onSide he'0 htg (onSide_of_mem_sideSet (Finset.min'_mem _ hnf))
  obtain ⟨Hg, hHg⟩ := WithTop.ne_top_iff_exists.mp hHgne
  have hHg' : npHgt X g (sideMin X g h e' hnf) = ((Hg : ℕ) : ℕ∞) := hHg.symm
  have hnz : (sideSet X R h e').Nonempty := sideSet_nonempty_gen X R h e'
  have htR : suppVal X R h e' ≠ ⊤ := suppVal_ne_top_of_monic hRm h e'
  have hHRne : npHgt X R (sideMin X R h e' hnz) ≠ ⊤ :=
    npHgt_ne_top_of_onSide he'0 htR (onSide_of_mem_sideSet (Finset.min'_mem _ hnz))
  obtain ⟨HR, hHR⟩ := WithTop.ne_top_iff_exists.mp hHRne
  have hHR' : npHgt X R (sideMin X R h e' hnz) = ((HR : ℕ) : ℕ∞) := hHR.symm
  -- B.39a §7: the product's side data
  have hnfz : (sideSet X (g * R) h e').Nonempty := sideSet_nonempty_gen X (g * R) h e'
  have hminmul : sideMin X (g * R) h e' hnfz
      = sideMin X g h e' hnf + sideMin X R h e' hnz :=
    sideMin_mul_gen hπ isKey_X hh0 he'0 hcop htg htR hnf hnz hHg' hHR' hnfz
  have hsdmul : sideDeg X (g * R) h e' hnfz = d + sideDeg X R h e' hnz :=
    sideDeg_mul_gen hπ isKey_X hh0 he'0 hcop htg htR hnf hnz hHg' hHR' hnfz
  have hnpmul : npHgt X (g * R) (sideMin X g h e' hnf + sideMin X R h e' hnz)
      = ((Hg + HR : ℕ) : ℕ∞) :=
    npHgt_mul_gen hπ isKey_X hh0 he'0 hcop htg htR hnf hnz hHg' hHR'
  have hrpmul : resPoly π X (g * R) h e' hnfz (Hg + HR)
      = resPoly π X g h e' hnf Hg * resPoly π X R h e' hnz HR :=
    resPoly_mul_gen hπ isKey_X hh0 he'0 hcop htg htR hnf hnz hHg' hHR' hnfz
  -- the class residual IS the product residual (through the lift identification)
  have hseteq : sideSet X (monicPoly a) h e' = sideSet X (g * R) h e' := by rw [heq]
  have hne2 : (sideSet X (monicPoly a) h e').Nonempty := by
    rw [hseteq]
    exact hnfz
  have hmineq : sideMin X (monicPoly a) h e' hne2 = sideMin X (g * R) h e' hnfz :=
    sideMin_congr heq hne2 hnfz
  have hH2 : npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne2)
      = ((Hg + HR : ℕ) : ℕ∞) := by
    rw [hmineq, heq, hminmul]
    exact hnpmul
  have hcrp : classResidualPoly π c h e' = resPoly π X (monicPoly a) h e' hne2 (Hg + HR) :=
    classResidualPoly_eq hπ he'0 hvis ha hne2 hH2
  have hirr' : Irreducible (resPoly π X g h e' hnf Hg * resPoly π X R h e' hnz HR) := by
    rw [← hrpmul, ← resPoly_congr heq hne2 hnfz (Hg + HR), ← hcrp]
    exact hirr₃
  -- the unit analysis: the rest's residual is a unit, the block's is THE residual
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hgdeg : (resPoly π X g h e' hnf Hg).natDegree = d :=
    (natDegree_resPoly hπ isKey_X he'0 hcop htg hnf hHg').1
  have hRdeg : (resPoly π X R h e' hnz HR).natDegree = sideDeg X R h e' hnz :=
    (natDegree_resPoly hπ isKey_X he'0 hcop htR hnz hHR').1
  have hnotu : ¬ IsUnit (resPoly π X g h e' hnf Hg) := by
    intro hu
    have h5 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  have huR : IsUnit (resPoly π X R h e' hnz HR) :=
    (hirr'.isUnit_or_isUnit rfl).resolve_left hnotu
  have hirrg : Irreducible (resPoly π X g h e' hnf Hg) := by
    obtain ⟨u, hu_eq⟩ := huR
    have hassoc1 : Associated (resPoly π X g h e' hnf Hg)
        (resPoly π X g h e' hnf Hg * resPoly π X R h e' hnz HR) :=
      ⟨u, by rw [hu_eq]⟩
    exact (Associated.symm hassoc1).irreducible hirr'
  -- NEW OUTPUT (i): the cofactor's side degree is 0, so the class residual has degree `d`
  have hsdR : sideDeg X R h e' hnz = 0 := by
    have h5 := Polynomial.natDegree_eq_zero_of_isUnit huR
    omega
  have htop2 : suppVal X (monicPoly a) h e' ≠ ⊤ :=
    suppVal_ne_top_of_monic (monicPoly_monic a) h e'
  have hcrpd : (classResidualPoly π c h e').natDegree = d := by
    rw [hcrp, (natDegree_resPoly hπ isKey_X he'0 hcop htop2 hne2 hH2).1,
      sideDeg_congr heq hne2 hnfz, hsdmul, hsdR]
    omega
  -- the residue pin `ḡ = X̄^(e'·d)` (unique factorization in `κ[X]`)
  have hres : (monicPoly a).map (residue O) = X ^ m := by
    have h5 := hstr a ha
    exact h5
  have hmapmul : g.map (residue O) * R.map (residue O) = X ^ m := by
    rw [← Polynomial.map_mul, ← heq]
    exact hres
  have hdvd : g.map (residue O) ∣ (X : Polynomial (ResidueField O)) ^ m :=
    ⟨R.map (residue O), hmapmul.symm⟩
  obtain ⟨k, hkm, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X m).mp hdvd
  have heqg : g.map (residue O) = X ^ k :=
    Polynomial.eq_of_monic_of_associated (hgm.map _) (Polynomial.monic_X_pow k) hassoc
  have hk : k = g.natDegree := by
    have h5 := congrArg Polynomial.natDegree heqg
    rw [hgm.natDegree_map, Polynomial.natDegree_X_pow] at h5
    exact h5.symm
  have hgres : g.map (residue O) = X ^ (e' * d) := by
    rw [heqg, hk, hsdg]
  -- fire the unconditional leaf law: the block's type is pinned
  have htyg : typeOf g = ⟨{(e', d)}⟩ :=
    Uniformity.Density.IFCG37.residualLeafLaw_all he'0 hd0 O π hπ h hh0 hcop g hgm
      hgpure hnf rfl hgres Hg hHg' hirrg
  -- degree bookkeeping
  have hdegsum : g.natDegree + R.natDegree = m := by
    have h6 : (monicPoly a).natDegree = m := monicPoly_natDegree a
    rw [heq, Polynomial.Monic.natDegree_mul hgm hRm] at h6
    exact h6
  have he'dm : e' * d < m := by omega
  have hRdeg' : R.natDegree = m - e' * d := by omega
  -- the pinned data decomposition
  have hdata' : σ.data = (e', d) ::ₘ (typeOf R).data := by
    rw [hdata, htyg]
    exact Multiset.singleton_add _ _
  -- NEW OUTPUT (ii): the cofactor's side collapses to its monic point
  -- the face's right endpoint `m` is on-side for the lift
  obtain ⟨hOm, -⟩ := onSide_monicPoly_of_npAttains hπ he'0 hvis hAm ha
  have hmmem : m ∈ sideSet X (monicPoly a) h e' := by
    refine mem_sideSet_iff'.mpr ⟨?_, hOm⟩
    rw [monicPoly_natDegree]
    omega
  have hmaxF : sideMax X (monicPoly a) h e' hne2 = m := by
    refine le_antisymm ?_ (Finset.le_max' _ _ hmmem)
    refine Finset.max'_le _ _ _ ?_
    intro y hy
    have h3 := (mem_sideSet_iff'.mp hy).1
    have h4 : (monicPoly a).natDegree = m := monicPoly_natDegree a
    omega
  -- `sideMax = sideMin + e'·sideDeg` on the lift pins `sideMin R = m − e'·d`
  have hmaxeqF := sideMax_eq he'0 hcop htop2 hne2
  have hsdF : sideDeg X (monicPoly a) h e' hne2 = d := by
    rw [sideDeg_congr heq hne2 hnfz, hsdmul, hsdR]
    omega
  have hminF : sideMin X (monicPoly a) h e' hne2 = m - e' * d := by
    rw [hmaxF, hsdF] at hmaxeqF
    omega
  have hminR : sideMin X R h e' hnz = R.natDegree := by
    rw [hmineq, hminmul, hming, zero_add] at hminF
    omega
  have hmaxR : sideMax X R h e' hnz = R.natDegree := by
    have h5 := sideMax_eq he'0 hcop htR hnz
    rw [hminR, hsdR, Nat.mul_zero, Nat.add_zero] at h5
    exact h5
  have hside : sideSet X R h e' = {R.natDegree} := by
    ext j
    rw [Finset.mem_singleton]
    constructor
    · intro hj
      have h5 : sideMin X R h e' hnz ≤ j := Finset.min'_le _ _ hj
      have h6 : j ≤ sideMax X R h e' hnz := Finset.le_max' _ _ hj
      omega
    · rintro rfl
      have h5 : sideMax X R h e' hnz ∈ sideSet X R h e' := Finset.max'_mem _ hnz
      rwa [hmaxR] at h5
  exact ⟨g, R, d, heq, hgm, hRm, hgpure, hd0, hsdg, he'dm, htyg, hRdeg', hdata',
    hcrpd, hside⟩

/-- ★ **THE STRICT CONE** (the steepness seed in coefficient form): a monic
polynomial whose `(h, e')`-side is the single monic point has EVERY proper
abscissa strictly above the face line — `h·(deg R − j) < e' · v(R_j)` in `ℕ∞`.
This is the exact cofactor carrier of the sub-face convolution: the two blocks'
slope ranges are disjoint, lift-side exact. -/
theorem strict_cone_of_side_singleton {R : Polynomial O} (hRm : R.Monic)
    {h e' : ℕ} (hside : sideSet X R h e' = {R.natDegree}) {j : ℕ}
    (hj : j < R.natDegree) :
    ((h * (R.natDegree - j) : ℕ) : ℕ∞) < e' • npHgt X R j := by
  -- the support value is `h · deg R` (the monic point is on-side)
  have hrmem : R.natDegree ∈ sideSet X R h e' := by
    rw [hside]
    exact Finset.mem_singleton_self _
  have hOr : OnSide X R h e' R.natDegree := onSide_of_mem_sideSet hrmem
  have hsupp : suppVal X R h e' = ((h * R.natDegree : ℕ) : ℕ∞) := by
    have h1 : e' • npHgt X R R.natDegree + ((h * R.natDegree : ℕ) : ℕ∞)
        = suppVal X R h e' := hOr
    rw [npHgt_monic_top hRm, smul_zero, zero_add] at h1
    exact h1.symm
  -- `j` is not on-side, and the support value bounds from below
  have hnot : ¬ OnSide X R h e' j := by
    intro hO
    have hjm : j ∈ sideSet X R h e' := mem_sideSet_iff'.mpr ⟨by omega, hO⟩
    rw [hside, Finset.mem_singleton] at hjm
    omega
  have hle : suppVal X R h e' ≤ e' • npHgt X R j + ((h * j : ℕ) : ℕ∞) := by
    rw [suppVal]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  have hlt : suppVal X R h e' < e' • npHgt X R j + ((h * j : ℕ) : ℕ∞) :=
    lt_of_le_of_ne hle (fun hcon => hnot hcon.symm)
  -- cancel the finite `h·j`
  have hsplit : (h * R.natDegree : ℕ) = h * (R.natDegree - j) + h * j := by
    have : R.natDegree - j + j = R.natDegree := Nat.sub_add_cancel (by omega)
    calc h * R.natDegree = h * (R.natDegree - j + j) := by rw [this]
      _ = h * (R.natDegree - j) + h * j := by ring
  rw [hsupp, hsplit, Nat.cast_add] at hlt
  exact (WithTop.add_lt_add_iff_right (ENat.coe_ne_top _)).mp hlt

/-- ★ **THE CLASS-SIDE STRICT CONE**: a monic polynomial whose `(h, e')`-side is
its single monic point has its canonical CLASS (at any window `N ≥ deg R`)
strictly above the face line coordinatewise — `h·(deg R − j) < e'·resOrd` at every
coordinate.  The windowed read either sees the true valuation exactly (below the
window) or saturates at `N`, and the face line sits below `e'·N` either way. -/
theorem class_strict_cone_of_side_singleton {π : O} (hπ : Irreducible π)
    {R : Polynomial O} (hRm : R.Monic) {h e' : ℕ} (hhe : h < e')
    (hside : sideSet X R h e' = {R.natDegree}) {N : ℕ} (hrN : R.natDegree ≤ N)
    (j : Fin R.natDegree) :
    h * (R.natDegree - (j : ℕ))
      < e' * resOrd (proj O R.natDegree N (fun i => R.coeff (i : ℕ)) j) := by
  have hr0 : 0 < R.natDegree := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hmp : monicPoly (fun i : Fin R.natDegree => R.coeff (i : ℕ)) = R :=
    monicPoly_coeff_eq_self hRm rfl
  have ha : proj O R.natDegree N (fun i : Fin R.natDegree => R.coeff (i : ℕ))
      = proj O R.natDegree N (fun i : Fin R.natDegree => R.coeff (i : ℕ)) := rfl
  -- the lift-side strict cone at the canonical lift
  have hstrict := strict_cone_of_side_singleton hRm hside j.isLt
  -- the saturated-window escape: the face line is below `e'·N` outright
  have hlineN : h * (R.natDegree - (j : ℕ)) < e' * N := by
    have h1 : h * (R.natDegree - (j : ℕ)) ≤ h * R.natDegree :=
      Nat.mul_le_mul_left h (Nat.sub_le _ _)
    have h2 : h * R.natDegree < e' * R.natDegree :=
      (Nat.mul_lt_mul_right hr0).mpr hhe
    have h3 : e' * R.natDegree ≤ e' * N := Nat.mul_le_mul_left e' hrN
    omega
  -- the windowed class read IS the target `resOrd` (definitional + Fin eta)
  have hcr : classCoeffVal
      (proj O R.natDegree N (fun i : Fin R.natDegree => R.coeff (i : ℕ)))
      ⟨(j : ℕ), j.isLt⟩
      = resOrd (proj O R.natDegree N
          (fun i : Fin R.natDegree => R.coeff (i : ℕ)) j) := rfl
  by_cases hlt : classCoeffVal
      (proj O R.natDegree N (fun i : Fin R.natDegree => R.coeff (i : ℕ)))
      ⟨(j : ℕ), j.isLt⟩ < N
  · -- the windowed read is exact: the class valuation IS the lift valuation
    have heq := npHgt_monicPoly_eq hπ ha j.isLt hlt
    rw [hmp] at heq
    rw [heq, nsmul_eq_mul, ← Nat.cast_mul] at hstrict
    have h5 : h * (R.natDegree - (j : ℕ)) < e' * classCoeffVal
        (proj O R.natDegree N (fun i : Fin R.natDegree => R.coeff (i : ℕ)))
        ⟨(j : ℕ), j.isLt⟩ := by exact_mod_cast hstrict
    rwa [hcr] at h5
  · -- the window saturates: `resOrd = N` and the escape fires
    have h7 : resOrd (proj O R.natDegree N
        (fun i : Fin R.natDegree => R.coeff (i : ℕ)) j) ≤ N :=
      resOrd_le _
    have h8 : resOrd (proj O R.natDegree N
        (fun i : Fin R.natDegree => R.coeff (i : ℕ)) j) = N := by
      omega
    rwa [h8]

/-- ★★ **THE COFACTOR READ, class-side** (the fibering's forward half): every lift
of a sub-face leaf cell at the minimal face `(h, e')` yields the canonical pair —
the pinned face block (`typeOf g = ⟨{(e', d)}⟩`) and the cofactor `R` of pinned
smaller mass `m − e'·d` and pinned type mass (`σ.data = (e', d) ::ₘ (typeOf R).data`)
whose canonical CLASS lies STRICTLY above the face line at every coordinate.  This
is the exact carrier shape of the steep smaller-mass census against which the
successor count unit convolves the face digit box. -/
theorem subface_cofactor_class {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ leafSubSector O π m σ M) {h e' : ℕ} (hF : MinFaceAt c h e')
    {a : Fin m → O} (ha : proj O m (M + m) a = c) :
    ∃ (g R : Polynomial O) (d : ℕ), monicPoly a = g * R ∧ g.Monic ∧ R.Monic
      ∧ IsPure X g h e' ∧ 0 < d ∧ g.natDegree = e' * d ∧ e' * d < m
      ∧ typeOf g = ⟨{(e', d)}⟩ ∧ R.natDegree = m - e' * d
      ∧ σ.data = (e', d) ::ₘ (typeOf R).data
      ∧ ∀ j : Fin R.natDegree,
          h * (R.natDegree - (j : ℕ))
            < e' * resOrd (proj O R.natDegree (M + m)
                (fun i => R.coeff (i : ℕ)) j) := by
  obtain ⟨g, R, d, heq, hgm, hRm, hgpure, hd0, hgd, hdm, htyg, hRdeg, hdata,
    -, hside⟩ := subface_transport_pinned hπ hm0 hc hF ha
  have hhe : h < e' := hF.2.1
  have hrN : R.natDegree ≤ M + m := by omega
  exact ⟨g, R, d, heq, hgm, hRm, hgpure, hd0, hgd, hdm, htyg, hRdeg, hdata,
    fun j => class_strict_cone_of_side_singleton hπ hRm hhe hside hrN j⟩

/-- ★ **The lift-free frame read**: a sub-face leaf cell at minimal face `(h, e')`
carries the CLASS-residual degree `d := (classResidualPoly π c h e').natDegree`
with `0 < d`, `e' * d < m`, and `(e', d) ∈ σ.data` — the frame `(h, e', d)` is a
function of the cell alone. -/
theorem subface_frame_read {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ leafSubSector O π m σ M) {h e' : ℕ} (hF : MinFaceAt c h e') :
    0 < (classResidualPoly π c h e').natDegree
      ∧ e' * (classResidualPoly π c h e').natDegree < m
      ∧ (e', (classResidualPoly π c h e').natDegree) ∈ σ.data := by
  obtain ⟨a, ha⟩ := proj_surjective O m (M + m) c
  obtain ⟨g, R, d, -, -, -, -, hd0, -, hdm, -, -, hdata, hcrpd, -⟩ :=
    subface_transport_pinned hπ hm0 hc hF ha
  rw [hcrpd]
  refine ⟨hd0, hdm, ?_⟩
  rw [hdata]
  exact Multiset.mem_cons_self _ _

end Transport

/-! ## §2 — ★★ THE FRAME PARTITION: the sub-face sector tiles by `(h, e', d)` -/

section Frames

/-- **The sub-face frame index**: all `(h, e', d)` with `1 ≤ h < e'` coprime,
`1 ≤ d`, `e'·d < m` (the face is PROPER — its block does not span), and `(e', d)`
an entry of the class type (TBT's `face_block_mem_type` forcing).  The range
bounds are implied: `e'·d < m` with `1 ≤ d` forces `e' < m`, and `h < e'`. -/
def subFrames (m : ℕ) (σ : FactorizationType) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    (fun p => 1 ≤ p.1 ∧ p.1 < p.2.1 ∧ Nat.gcd p.1 p.2.1 = 1 ∧ 1 ≤ p.2.2
      ∧ p.2.1 * p.2.2 < m ∧ (p.2.1, p.2.2) ∈ σ.data)

/-- Frame membership is exactly the six arithmetic clauses. -/
theorem mem_subFrames_iff {m : ℕ} {σ : FactorizationType} {p : ℕ × ℕ × ℕ} :
    p ∈ subFrames m σ
      ↔ 1 ≤ p.1 ∧ p.1 < p.2.1 ∧ Nat.Coprime p.1 p.2.1 ∧ 1 ≤ p.2.2
        ∧ p.2.1 * p.2.2 < m ∧ (p.2.1, p.2.2) ∈ σ.data := by
  unfold subFrames
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    have he'le : p.2.1 ≤ p.2.1 * p.2.2 := Nat.le_mul_of_pos_right _ (by omega)
    have hdle : p.2.2 ≤ p.2.1 * p.2.2 := Nat.le_mul_of_pos_left _ (by omega)
    refine ⟨?_, h1, h2, h3, h4, h5, h6⟩
    rw [Finset.mem_product, Finset.mem_product]
    refine ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩

/-- **The first open instance, pinned** (kernel-decided): at LSC's hand-checked
witness data `m = 5`, `σ = ⟨{(4,1), (1,1)}⟩` (the type of the heights-`(2,1,1,1,1)`
cell), the admissible frames are exactly the two slope-`h/4` faces — the block
`(e', d) = (4, 1)` at `h ∈ {1, 3}`.  (`(1,1)` contributes no frame: `e' = 1`
admits no `h < e'`.) -/
theorem subFrames_five_witness :
    subFrames 5 ⟨{(4, 1), (1, 1)}⟩ = {(1, 4, 1), (3, 4, 1)} := by decide

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The per-frame sub-face cell carrier**: the sub-face leaf cells whose (unique)
minimal face is `(h, e')` with class-residual degree `d`. -/
def subfaceCell (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m h e' d : ℕ) (σ : FactorizationType)
    (M : ℕ) : Set (Coeff O m (M + m)) :=
  {c | c ∈ leafSubSector O π m σ M ∧ MinFaceAt c h e'
    ∧ (classResidualPoly π c h e').natDegree = d}

/-- ★★ **THE PARTITION** (set form): the sub-face sector IS the disjoint union of
the per-frame cells over the admissible frames — every sub-face cell has a unique
minimal face, its residual degree is a lift-free read, and §1's transport pins the
frame data inside `subFrames`. -/
theorem leafSubSector_eq_biUnion {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    (σ : FactorizationType) (M : ℕ) :
    leafSubSector O π m σ M
      = ⋃ p ∈ subFrames m σ, subfaceCell O π m p.1 p.2.1 p.2.2 σ M := by
  ext c
  constructor
  · intro hc
    obtain ⟨hcar, h, e', hF, hirr, hnA0⟩ := hc
    have hc' : c ∈ leafSubSector O π m σ M := ⟨hcar, h, e', hF, hirr, hnA0⟩
    obtain ⟨hd0, hdm, hmem⟩ := subface_frame_read hπ hm0 hc' hF
    have hframe : (h, e', (classResidualPoly π c h e').natDegree) ∈ subFrames m σ :=
      mem_subFrames_iff.mpr ⟨hF.1, hF.2.1, hF.2.2.1, hd0, hdm, hmem⟩
    exact Set.mem_biUnion hframe ⟨hc', hF, rfl⟩
  · intro hc
    rw [Set.mem_iUnion₂] at hc
    obtain ⟨p, hp, hcp⟩ := hc
    exact hcp.1

/-- The per-frame cells at distinct frames are disjoint (the minimal face is
unique and the residual degree is a function of the cell). -/
theorem subfaceCell_disjoint {π : O} {m : ℕ} {p p' : ℕ × ℕ × ℕ} (hne : p ≠ p')
    (σ : FactorizationType) (M : ℕ) :
    Disjoint (subfaceCell O π m p.1 p.2.1 p.2.2 σ M)
      (subfaceCell O π m p'.1 p'.2.1 p'.2.2 σ M) := by
  rw [Set.disjoint_left]
  rintro c ⟨-, hF, hd⟩ ⟨-, hF', hd'⟩
  obtain ⟨hh, he⟩ := minFaceAt_unique hF hF'
  refine hne ?_
  have hdd : p.2.2 = p'.2.2 := by
    rw [← hd, ← hd', hh, he]
  obtain ⟨h₁, e₁, d₁⟩ := p
  obtain ⟨h₂, e₂, d₂⟩ := p'
  dsimp only at hh he hdd
  rw [hh, he, hdd]

/-- ★★ **THE PARTITION COUNT**: the sub-face count is the exact frame sum, at
every level, every uniformizer. -/
theorem leafSubCount_eq_sum_frames {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm0 : 0 < m) (σ : FactorizationType) (M : ℕ) :
    leafSubCount O π m σ M
      = ∑ p ∈ subFrames m σ,
          Nat.card (subfaceCell O π m p.1 p.2.1 p.2.2 σ M) := by
  rw [show leafSubCount O π m σ M = Nat.card (leafSubSector O π m σ M) from rfl,
    leafSubSector_eq_biUnion hπ hm0 σ M, Nat.card_coe_set_eq,
    ncard_biUnion_eq _ _ (fun p _ p' _ hne => subfaceCell_disjoint hne σ M)]
  exact Finset.sum_congr rfl fun p _ => (Nat.card_coe_set_eq _).symm

/-- ★ **Off-frame emptiness** (the partition's completeness, in consumable form):
at any `(h, e', d)` OUTSIDE the admissible frame index the per-frame cell is
EMPTY — so a census may sum over `subFrames` alone with nothing lost. -/
theorem subfaceCell_eq_empty_of_not_mem {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm0 : 0 < m) {σ : FactorizationType} {h e' d : ℕ}
    (hnot : (h, e', d) ∉ subFrames m σ) (M : ℕ) :
    subfaceCell O π m h e' d σ M = (∅ : Set (Coeff O m (M + m))) := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hc, hF, hd⟩
  obtain ⟨hd0, hdm, hmem⟩ := subface_frame_read hπ hm0 hc hF
  rw [hd] at hd0 hdm hmem
  exact hnot (mem_subFrames_iff.mpr ⟨hF.1, hF.2.1, hF.2.2.1, hd0, hdm, hmem⟩)

end Frames

/-! ## §3 — ★★ THE PER-FRAME LAWS and the row-5 reduction fire -/

section Laws

/-- ★★ **THE PER-FRAME LAW — `SubfaceFrameLaw m h e' d σ`**: the uniform rational
limit of the normalized per-frame sub-face cell count.  The frames in
`subFrames m σ` are row 5's exact per-axis content after this file: the face
digit box at `(h, e', d)` (LSC's necklace territory at mass `e'·d`) convolved
with the steep mass-`(m − e'·d)` cofactor census through the pinned-depth
`q^{h·d·(m − e'·d)}` clusters (CSL/RDC territory). -/
def SubfaceFrameLaw (m h e' d : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (Nat.card (subfaceCell O π m h e' d σ M) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- ★★★ **THE ROW-5 REDUCTION FIRE**: `LeafSubfaceLaw m σ` from the finitely many
per-frame laws — the leaf row's remaining content is exactly the per-frame family.
(`ZcURLim_sum` over the frame index + the exact partition count.) -/
theorem leafSubfaceLaw_of_frameLaws {m : ℕ} (hm0 : 0 < m) (σ : FactorizationType)
    (hlaws : ∀ p ∈ subFrames m σ, SubfaceFrameLaw m p.1 p.2.1 p.2.2 σ) :
    LeafSubfaceLaw m σ := by
  refine (ZcURLim_sum (subFrames m σ)
    (fun p => fun O _ _ _ _ _ π M =>
      (Nat.card (subfaceCell O π m p.1 p.2.1 p.2.2 σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) hlaws).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (∑ p ∈ subFrames m σ,
      (Nat.card (subfaceCell O π m p.1 p.2.1 p.2.2 σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))
    = (leafSubCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [leafSubCount_eq_sum_frames hπ hm0 σ M]
  push_cast
  rw [Finset.sum_div]

end Laws

/-! ## §4 — ★★★ THE MASTERS RECOMPUTED: the leaf row re-based on the per-frame
family

IFCG59's masters consumed `LeafSubfaceLaw e σ` under the guards + non-singleton σ.
§3's reduction fire re-bases that row onto the finitely many per-frame laws
`SubfaceFrameLaw e h e' d σ`, `(h, e', d) ∈ subFrames e σ` — strictly finer
content (the joint law is their sum through the exact partition). -/

section Masters

open Uniformity.Density.IFCG38 (SplitConvolutionDefectLaw)
open Uniformity.Density.IFCG44 (PowerConvolutionDefectLaw PowerFullSpanLaw)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG51 (EisFullSpanRemainderLaw)
open Uniformity.Density.IFCG58 (VisCensusLaw)

/-- ★★★ **THE CENSUS MASTER ON PCD's SPINE, LEAF ROW ON FRAMES**: IFCG59's
`decidedSliceAt_all_of_visCensus'` with the leaf premise re-based to the
per-frame family. -/
theorem decidedSliceAt_all_of_visCensus_frames
    (hVC : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ∀ g, VisCensusLaw g e σ)
    (hPF : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerFullSpanLaw e σ)
    (hFrame : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ p ∈ subFrames e σ, SubfaceFrameLaw e p.1 p.2.1 p.2.2 σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG59.decidedSliceAt_all_of_visCensus' hVC hPF
    (fun e he hsm σ hσ hwit hram hcard =>
      leafSubfaceLaw_of_frameLaws (by omega : 0 < e) σ
        (hFrame e he hsm σ hσ hwit hram hcard))
    hR4

/-- ★★★ **THE CENSUS MASTER ON LSC's SPINE, LEAF ROW ON FRAMES**: IFCG59's
`decidedSliceAt_all_of_MASTER''` with the leaf premise re-based to the per-frame
family — the surviving premise surface of the census is now
{`FactorCorrespondenceAt` (row 1, THE staged cite), `EisFullSpanRemainderLaw`
(row 2), `SplitConvolutionDefectLaw` (row 3), `PowerConvolutionDefectLaw`
(row 4), **`SubfaceFrameLaw e h e' d σ` at the admissible frames** (row 5)}. -/
theorem decidedSliceAt_all_of_MASTER_FRAMES
    (hFC : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerConvolutionDefectLaw e σ)
    (hFrame : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ p ∈ subFrames e σ, SubfaceFrameLaw e p.1 p.2.1 p.2.2 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG59.decidedSliceAt_all_of_MASTER'' hFC hEis hSD hPD
    (fun e he hsm σ hσ hwit hram hcard =>
      leafSubfaceLaw_of_frameLaws (by omega : 0 < e) σ
        (hFrame e he hsm σ hσ hwit hram hcard))

universe uW uG uKt uL

/-- ★★★ **THE CAPSTONE MASTER, LEAF ROW ON FRAMES**: IFCG59's
`capstoneHypotheses_of_MASTER''` with the leaf premise re-based to the per-frame
family (ID12's honesty frame applies verbatim). -/
theorem capstoneHypotheses_of_MASTER_FRAMES (n : ℕ)
    (hladder : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ),
      CanonicalLadderConfig C B G Kt L N v ρ q n →
      Uniformity.Density.IFC5.LadderSupplyLive₃.{uW, uG, uKt, uL}
        C B G Kt L N v ρ q n)
    (hdeepTwist : ∀ (O : Type) [CommRing O] (K : Type) [Field K]
      (C : Ladder.SlotCarrier O K) (B : Ladder.BlockData C)
      (G : Type uG) [CommGroup G] (Kt : Type uKt) [Field Kt] (L : Type uL) [Field L]
      [Algebra Kt L] (N : Gauge.NormSection G) (v : ℕ → (G →* Multiplicative ℤ))
      (ρ : ∀ j : ℕ, MonoidHom.ker (v j) →* Lˣ) (q : ℕ → ℤ)
      (A : ℕ → Gauge.GaugeArena G Kt N) (R : ℕ → G → Kt) (w : ℕ → Ktˣ) (r : ℕ),
      CanonicalDeepTwistConfig C B G Kt L N v ρ q A R w r n →
      Ladder.DeepTwistConjunctLive r v ρ q A R w)
    (hFC : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hEis : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → EisFullSpanRemainderLaw m σ)
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerConvolutionDefectLaw e σ)
    (hFrame : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ p ∈ subFrames e σ, SubfaceFrameLaw e p.1 p.2.1 p.2.2 σ) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  Uniformity.Density.IFCG59.capstoneHypotheses_of_MASTER''.{uW, uG, uKt, uL} n
    hladder hdeepTwist hFC hEis hSD hPD
    (fun e he hsm σ hσ hwit hram hcard =>
      leafSubfaceLaw_of_frameLaws (by omega : 0 < e) σ
        (hFrame e he hsm σ hσ hwit hram hcard))

end Masters

end Uniformity.Density.IFCG66

end

/-! ## AXCHECK FOOTER — expected: `strict_cone_of_side_singleton` and
`subFrames_five_witness` are pure Lean core `{propext, Classical.choice,
Quot.sound}`; the transport/partition/law theorems are Lean core + EXACTLY the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42, inherited through IFCG59's split engine — never re-consumed); the two
census masters likewise; the capstone master additionally inherits exactly
`Uniformity.Density.Tower.agnprw_termination` (ID12's, previously declared).
The C.33 cites and `AX_cellRecursion` must NOT occur. -/

#print axioms Uniformity.Density.IFCG66.subface_transport_pinned
#print axioms Uniformity.Density.IFCG66.strict_cone_of_side_singleton
#print axioms Uniformity.Density.IFCG66.class_strict_cone_of_side_singleton
#print axioms Uniformity.Density.IFCG66.subface_cofactor_class
#print axioms Uniformity.Density.IFCG66.subface_frame_read
#print axioms Uniformity.Density.IFCG66.subFrames_five_witness
#print axioms Uniformity.Density.IFCG66.leafSubSector_eq_biUnion
#print axioms Uniformity.Density.IFCG66.subfaceCell_disjoint
#print axioms Uniformity.Density.IFCG66.subfaceCell_eq_empty_of_not_mem
#print axioms Uniformity.Density.IFCG66.leafSubCount_eq_sum_frames
#print axioms Uniformity.Density.IFCG66.leafSubfaceLaw_of_frameLaws
#print axioms Uniformity.Density.IFCG66.decidedSliceAt_all_of_visCensus_frames
#print axioms Uniformity.Density.IFCG66.decidedSliceAt_all_of_MASTER_FRAMES
#print axioms Uniformity.Density.IFCG66.capstoneHypotheses_of_MASTER_FRAMES
