/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG67

/-!
# Uniformity.ChapI.IFCG69 — [SFW 2026-08-31] `SubfaceFrameLaw` at the r = 1 frames:
the steep census, the drainage coupling, and the first non-singleton leaf law

Stage SFW of the cone census (design record `runs/wave-c/verdict_SFW.md`; consumes
LSF = `IFCG66` and DPN = `IFCG67`, and through them LSC = `IFCG57` and the spine).
DPN closed the depth pin `mixDepth = h·d·(m − e'·d)` and fired both CSL couplings;
the remainder for `SubfaceFrameLaw m h e' d σ` was (i) the steep census, (ii) the
shifted-level factor decidedness, (iii) the image characterization.  At the r = 1
frames (`m = e'·d + 1` — the steep cofactor is a single linear factor) ALL THREE
close UNCONDITIONALLY in this file:

* **§1 THE CARRIERS AND THEIR EXACT COUNTS**: `pinnedBox` (LSC's height cone with
  the corner pinned EXACTLY at `h·d` and irreducible digit polynomial — at `d = 1`
  a PROPER sub-box of `leafIrrBox`, which is why LSC's `leafIrrBox_corner` demanded
  `d ≥ 2`) with count `nz_d(q) · q^(e'd·K − wLeaf)` where `nz_d` counts the
  irreducible monic degree-`d` residue polynomials with NONZERO constant term
  (`= N_d(q)` for `d ≥ 2`; `= q − 1` at `d = 1`); and `steepLin` (the mass-1
  X-stratum = the r = 1 steep census: steepness `h·1 < e'·v` is exactly `1 ≤ v`
  under `h < e'`) with count `q^(K−1)` — the m = 1 decided census, exact at every
  level.
* **§2 THE PRODUCT PACKAGE** (the image characterization, forward): the `mulClass`
  of a pinned-box class and a steep linear class IS a sub-face leaf cell at frame
  `(h, e', d)` — the product coefficient identities `P_j = g_{j−1} + α·g_j` give
  the cone with the EXACT coordinate at `j = 1` and the strictly-raised corner;
  the face data, the residual (`resPoly` multiplicativity: the linear factor's
  side residual is a unit), the stratum/shallow/non-pure-face bookkeeping, and the
  DECIDEDNESS through DPN's `decidedAt_mulClass_of_cones` with its two shifted
  premises DISCHARGED — the box premise by the box's decision engine at the
  shifted window `N − h·d` (all box reads live at digit levels `≤ h·d`, stable
  under the shift), the linear premise by `typeOf_of_natDegree_one` (every mass-1
  class is decided `⟨{(1,1)}⟩`, outright).
* **§3 SURJECTIVITY**: LSF's pinned transport factors every cell through the
  carriers (the digit irreducibility travels BACKWARDS through LSC's bridge and
  the unit factorization of the residual).
* **§4 THE SEPARATION** (Hensel-free at r = 1): two carrier factorizations of one
  product class agree factorwise mod `π^(N − h·d)` — evaluate the product
  congruence at the steep root; the box forces `π^(h·d) ∥ g(−α)` exactly, pinning
  the roots together; the monic cancellation recovers the block side.  Hence the
  `mulClass` fiber over every cell is EXACTLY one `pairNbhd` cluster: size
  `q^(h·d)` by DPN's fiber law.
* **§5 THE COUNT AND THE LAW**: `#subfaceCell(N) · q^(h·d) = #pinnedBox · #steepLin`
  for `M ≥ h·d`, so the normalized count is EVENTUALLY THE CONSTANT
  `nz_d(q)/q^(wLeaf + h·d + 1)` — ★★★ `subfaceFrameLaw_r_one`:
  `SubfaceFrameLaw m h e' d σ` at EVERY r = 1 frame, UNCONDITIONAL (at mismatched
  σ the cell is provably empty and the law is the zero family).
* **§6 ★ THE WITNESS FIRES**: both `m = 5` witness frames `(1,4,1)/(3,4,1)` have
  r = 1 — `leafSubfaceLaw_five : LeafSubfaceLaw 5 ⟨{(4,1),(1,1)}⟩`, the FIRST
  non-singleton leaf law, machine-checked end-to-end.  Plus the three masters
  recomputed with the leaf row's premise restricted to the r ≥ 2 frames.

## Honest scope

NOT proved here (the exact remainder after this file): `SubfaceFrameLaw m h e' d σ`
at frames with `m − e'·d ≥ 2` — the steep census at mass `r ≥ 2` (the decided-τ
count in the strict cone, the fractional-slope analogue of the deep census) and the
r ≥ 2 separation engine (the one-root evaluation argument used here is specific to
a linear cofactor; the general case needs the Bezout/resultant gap).  Nothing is
weakened: `SubfaceFrameLaw`/`LeafSubfaceLaw`/the master statements are
byte-untouched upstream; the masters below STRENGTHEN IFCG66's (their leaf premise
is demanded only at the r ≥ 2 frames).

## Axiom fence (machine-exact at landing)

The §1 counts and the §4/§5 kit are pure Lean core `{propext, Classical.choice,
Quot.sound}`; everything consuming LSF's transport (§2 §3 §5 §6) inherits Lean core
+ EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, through IFCG66/IFCG67 —
never re-consumed); the capstone master additionally inherits
`Uniformity.Density.Tower.agnprw_termination` (ID12's, previously declared).  The
C.33 cites, `AX_cellRecursion`, and `sorryAx` must NOT occur.  Zero sorries at
landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG69

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFC7 (resOut mk_resOut)
open Uniformity.Density.IFCG4 (IrredOfDeg)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG17 (monicPoly_coeff_eq_self)
open Uniformity.Density.IFCG19 (necklacePoly necklacePoly_eval_card)
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport classNPSupport_le
  le_classCoeffVal_iff_dvd classCoeffVal_exact classCoeffVal_le)
open Uniformity.Density.IFCG22 (resOrd_mk_eq)
open Uniformity.Density.IFCG24 (npHeight_coe)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq addVal_eq_of_pow_dvd_not_dvd)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_sum ConeRemainderLaw
  shallowSet pureFaceSet faceBox faceH mem_stratum_X_pow_iff)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains mem_sideSet_of_onSide)
open Uniformity.Density.IFCG28 (classSideSet sideSet_monicPoly_eq sideMin_monicPoly_eq
  sideMax_monicPoly_eq)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_unique classResidualPoly
  classResidualPoly_eq)
open Uniformity.Density.IFCG36 (resDig resDig_mk resOrd_eq_iff_resDig card_setOf_resDig)
open Uniformity.Density.IFCG37 (decidedAt_of_spanning_irr)
open Uniformity.Density.IFCG38 (SplitConvolutionDefectLaw)
open Uniformity.Density.IFCG42 (pairNbhd)
open Uniformity.Density.IFCG44 (PowerConvolutionDefectLaw PowerFullSpanLaw)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG51 (EisFullSpanRemainderLaw)
open Uniformity.Density.IFCG57 (tLeaf tLeaf_le_iff tLeaf_le_corner wLeaf wLeaf_le_sq
  resAt resAt_lt leafDig leafResPoly leafResPoly_coeff_lt leafResPoly_coeff_top
  leafResPoly_natDegree leafResPoly_monic leafResPoly_eq_iff
  coeff_zero_ne_zero_of_irreducible leafCone leafIrrBox leafCone_face_data
  classResidualPoly_eq_leafResPoly irreducible_classResidualPoly_iff leafFiber
  mem_leafFiber_iff card_leafFiber leafGenre finite_leafGenre leafSubSector
  LeafSubfaceLaw)
open Uniformity.Density.IFCG58 (VisCensusLaw)
open Uniformity.Density.IFCG66 (subFrames mem_subFrames_iff subFrames_five_witness
  subfaceCell SubfaceFrameLaw subface_transport_pinned leafSubfaceLaw_of_frameLaws
  strict_cone_of_side_singleton class_strict_cone_of_side_singleton)
open Uniformity.Density.IFCG67 (cone_data_of_isPure natCard_pairNbhd_of_cones
  decidedAt_mulClass_of_cones)

attribute [local instance] Classical.propDecidable

/-! ## §0 — kit (private replicas of the established supply + two new small tools) -/

section Kit

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- Counting bridge (IFCG57's private helper, reproduced). -/
private theorem natCard_set_eq_card_filter {γ : Type*} [Fintype γ] (s : Set γ) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

/-- The fibre-partition helper (IFCG57's private helper, reproduced). -/
private theorem natCard_eq_sum_fiber {γ δ : Type*} [Fintype γ] (s : Set γ) (φ : γ → δ)
    (T : Finset δ) (hT : ∀ a ∈ s, φ a ∈ T) :
    Nat.card s = ∑ b ∈ T, Nat.card ((s ∩ φ ⁻¹' {b}) : Set γ) := by
  rw [natCard_set_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := φ) (t := T)
      (fun a ha => hT a (by simpa using (Finset.mem_filter.1 ha).2))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [natCard_set_eq_card_filter, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/-- The digit congruence (IFCG36's private replica): digits strictly below the
perturbation level are stable. -/
private theorem digAt_congr {π : O} (hπ : Irreducible π) {N k : ℕ} (hk : k < N)
    {x y : O} (h : π ^ N ∣ x - y) : digAt π k x = digAt π k y := by
  classical
  have hsub : π ^ k ∣ x - y := (pow_dvd_pow π hk.le).trans h
  have hsub1 : π ^ (k + 1) ∣ x - y := (pow_dvd_pow π (Nat.succ_le_of_lt hk)).trans h
  by_cases hx : π ^ k ∣ x
  · have hneg : π ^ k ∣ -(x - y) := (dvd_neg).2 hsub
    have hz : digAt π k (-(x - y)) = 0 := (digAt_eq_zero_iff hπ hneg).2 ((dvd_neg).2 hsub1)
    have hyx : y = x + -(x - y) := by ring
    rw [hyx, digAt_add hπ hx hneg, hz, add_zero]
  · have hy : ¬ π ^ k ∣ y := by
      intro hy
      refine hx ?_
      have hxy : x = y + (x - y) := by ring
      rw [hxy]
      exact dvd_add hy hsub
    simp only [digAt, dif_neg hx, dif_neg hy]

/-- **The monic cancellation**: a constant dividing a product with a MONIC factor
divides the cofactor, coefficientwise (pass to `O ⧸ (z)`, where the image of the
product vanishes and the monic factor is regular). -/
private theorem C_dvd_of_C_dvd_mul_monic {z : O} {S T : Polynomial O} (hT : T.Monic)
    (hdvd : Polynomial.C z ∣ S * T) : Polynomial.C z ∣ S := by
  classical
  set I := Ideal.span ({z} : Set O) with hI
  set φ := Ideal.Quotient.mk I with hφ
  have hcoeff : ∀ k, z ∣ (S * T).coeff k :=
    fun k => (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdvd k
  have hmap : (S * T).map φ = 0 := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem).2
      (by rw [hI]; exact Ideal.mem_span_singleton.2 (hcoeff k))
  rw [Polynomial.map_mul] at hmap
  have hTm : (T.map φ).Monic := hT.map φ
  have hS0 : S.map φ = 0 := by
    have hreg := hTm.isRegular.right
    have h0 : S.map φ * T.map φ = 0 * T.map φ := by rw [zero_mul]; exact hmap
    exact hreg h0
  refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun k => ?_
  have h1 : φ (S.coeff k) = 0 := by
    have h2 := congrArg (fun p => Polynomial.coeff p k) hS0
    simpa [Polynomial.coeff_map] using h2
  have h3 : S.coeff k ∈ I := (Ideal.Quotient.eq_zero_iff_mem).1 h1
  rw [hI] at h3
  exact Ideal.mem_span_singleton.1 h3

/-- Coefficientwise divisibility passes to evaluations. -/
private theorem dvd_eval_of_C_dvd {z : O} {P : Polynomial O} (h : Polynomial.C z ∣ P)
    (x : O) : z ∣ P.eval x := by
  obtain ⟨Q, hQ⟩ := h
  rw [hQ, Polynomial.eval_mul, Polynomial.eval_C]
  exact Dvd.intro _ rfl

/-- Equality of `mulClass` products gives `π^N`-divisibility of the lift-product
difference (IFCG41's private cancellation bridge, reproduced). -/
private theorem C_pow_dvd_mul_sub_of_mulClass_eq {π : O} (hπ : Irreducible π)
    {n₁ n₂ N : ℕ} {a₁ b₁ : Fin n₁ → O} {a₂ b₂ : Fin n₂ → O}
    (heq : mulClass (proj O n₁ N a₁) (proj O n₂ N a₂)
         = mulClass (proj O n₁ N b₁) (proj O n₂ N b₂)) :
    Polynomial.C (π ^ N) ∣ monicPoly b₁ * monicPoly b₂ - monicPoly a₁ * monicPoly a₂ := by
  refine (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i => ?_
  have hspan : (maximalIdeal O) ^ N = Ideal.span {π ^ N} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rcases Nat.lt_or_ge i (n₁ + n₂) with hi | hi
  · have h1 : proj O (n₁ + n₂) N (fun j => (monicPoly a₁ * monicPoly a₂).coeff (j : ℕ))
        = proj O (n₁ + n₂) N (fun j => (monicPoly b₁ * monicPoly b₂).coeff (j : ℕ)) := by
      rw [mulClass_proj, mulClass_proj, heq]
    have h2 := congrFun h1 ⟨i, hi⟩
    have h3 : (monicPoly b₁ * monicPoly b₂).coeff i - (monicPoly a₁ * monicPoly a₂).coeff i
        ∈ (maximalIdeal O) ^ N := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2.symm
    rw [hspan, Ideal.mem_span_singleton] at h3
    rw [Polynomial.coeff_sub]
    exact h3
  · have hd : (monicPoly a₁ * monicPoly a₂).natDegree = n₁ + n₂ := by
      rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂),
        monicPoly_natDegree, monicPoly_natDegree]
    have hd' : (monicPoly b₁ * monicPoly b₂).natDegree = n₁ + n₂ := by
      rw [(monicPoly_monic b₁).natDegree_mul (monicPoly_monic b₂),
        monicPoly_natDegree, monicPoly_natDegree]
    have e1 : (monicPoly b₁ * monicPoly b₂).coeff i
        = (monicPoly a₁ * monicPoly a₂).coeff i := by
      rcases eq_or_lt_of_le hi with heqi | hlt
      · rw [← heqi]
        have hb1 : (monicPoly b₁ * monicPoly b₂).coeff (n₁ + n₂) = 1 := by
          rw [← hd']
          exact ((monicPoly_monic b₁).mul (monicPoly_monic b₂)).coeff_natDegree
        have ha1 : (monicPoly a₁ * monicPoly a₂).coeff (n₁ + n₂) = 1 := by
          rw [← hd]
          exact ((monicPoly_monic a₁).mul (monicPoly_monic a₂)).coeff_natDegree
        rw [hb1, ha1]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd']; exact hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hlt)]
    rw [Polynomial.coeff_sub, e1, sub_self]
    exact dvd_zero _

/-- The mass-1 monic frame, explicitly: `monicPoly a = X + C (a 0)`. -/
private theorem monicPoly_one_eq (a : Fin 1 → O) :
    monicPoly a = Polynomial.X + Polynomial.C (a 0) := by
  unfold monicPoly
  rw [Fin.sum_univ_one]
  simp

/-- The monic top point has height `0` (IFCG66's private replica). -/
private theorem npHgt_monic_top {g : Polynomial O} (hg : g.Monic) :
    npHgt X g g.natDegree = 0 := by
  rw [npHgt_X, hg.coeff_natDegree]
  exact IsDiscreteValuationRing.addVal_one

/-- A monic polynomial's cleared support value is finite (IFCG66's private replica). -/
private theorem suppVal_ne_top_of_monic {g : Polynomial O} (hg : g.Monic) (u ℓ : ℕ) :
    suppVal X g u ℓ ≠ ⊤ := by
  have hle : suppVal X g u ℓ ≤ ℓ • npHgt X g g.natDegree + ((u * g.natDegree : ℕ) : ℕ∞) := by
    rw [suppVal]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  rw [npHgt_monic_top hg, smul_zero, zero_add] at hle
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle

/-- `classSideSet` membership through the Classical filter (IFCG57's private replica). -/
private theorem mem_classSideSet_iff' {m K : ℕ} {c : Coeff O m K} {u ℓ j : ℕ} :
    j ∈ classSideSet c u ℓ ↔ (j < m + 1 ∧ NPAttains c u ℓ j) := by
  classical
  constructor
  · intro hj
    have hj' : j ∈ Finset.filter (NPAttains c u ℓ) (Finset.range (m + 1)) := hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj'
    exact ⟨Finset.mem_range.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    have h3 : j ∈ Finset.filter (NPAttains c u ℓ) (Finset.range (m + 1)) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩
    exact h3

private theorem sideMin_congr {u ℓ : ℕ} {f₁ f₂ : Polynomial O} (hf : f₁ = f₂)
    (hn1 : (sideSet X f₁ u ℓ).Nonempty) (hn2 : (sideSet X f₂ u ℓ).Nonempty) :
    sideMin X f₁ u ℓ hn1 = sideMin X f₂ u ℓ hn2 := by
  subst hf
  rfl

private theorem resPoly_congr {π : O} {u ℓ : ℕ} {f₁ f₂ : Polynomial O} (hf : f₁ = f₂)
    (hn1 : (sideSet X f₁ u ℓ).Nonempty) (hn2 : (sideSet X f₂ u ℓ).Nonempty) (H : ℕ) :
    resPoly π X f₁ u ℓ hn1 H = resPoly π X f₂ u ℓ hn2 H := by
  subst hf
  rfl

end Kit

/-! ## §1 — the two carriers of the r = 1 convolution and their EXACT counts -/

section Carriers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The corner-pinned face box**: LSC's height cone with the corner valuation
EXACTLY `h·d` and irreducible digit polynomial.  For `d ≥ 2` this is `leafIrrBox`
(the corner pin is automatic, `leafIrrBox_corner`); at `d = 1` it is the proper
sub-box that the transport image actually fills. -/
def pinnedBox (π : O) (K h e' d : ℕ) : Set (Coeff O (e' * d) K) :=
  {γ | γ ∈ leafCone O (e' * d) K h e' ∧ resOrd (resAt γ 0) = h * d
    ∧ Irreducible (leafResPoly π h e' d γ)}

/-- **The steep linear census carrier** (the r = 1 steep census): the mass-1
classes in the X-stratum.  Under `h < e'` this IS the strict cone
`h·(1 − 0) < e'·v₀`. -/
def steepLin (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : ℕ) : Set (Coeff O 1 K) :=
  {ρ | 1 ≤ resOrd (ρ 0)}

/-- ★ **The m = 1 census count**: `q^(K−1)` steep linear classes at every level —
the r = 1 steep census is exact (IFCG36's digit level-set count at the bottom
digit). -/
theorem card_steepLin {π : O} (hπ : Irreducible π) {K : ℕ} (hK : 1 ≤ K) :
    Nat.card (steepLin O K) = residueCard O ^ (K - 1) := by
  classical
  have hset : {x : Res O K | 1 ≤ resOrd x}
      = {x : Res O K | 0 ≤ resOrd x ∧ resDig π 0 x = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Nat.zero_le, true_and]
    have hxout : Ideal.Quotient.mk ((maximalIdeal O) ^ K) (resOut x) = x := mk_resOut x
    have h1 : 1 ≤ resOrd x ↔ π ^ 1 ∣ resOut x := by
      conv_lhs => rw [← hxout]
      exact resOrd_ge_iff hπ hK (resOut x)
    have h2 : resDig π 0 x = 0 ↔ π ^ (0 + 1) ∣ resOut x := by
      show digAt π 0 (resOut x) = 0 ↔ _
      exact digAt_eq_zero_iff hπ (by rw [pow_zero]; exact one_dvd _)
    rw [h1, h2, zero_add]
  have hequiv : Nat.card (steepLin O K)
      = Nat.card ({x : Res O K | 1 ≤ resOrd x} : Set (Res O K)) := by
    refine Nat.card_congr ?_
    refine ⟨fun p => ⟨p.1 0, p.2⟩, fun x => ⟨fun _ => x.1, x.2⟩, ?_, ?_⟩
    · intro p
      refine Subtype.ext (funext fun i => ?_)
      rw [Subsingleton.elim i 0]
    · intro x
      rfl
  rw [hequiv, hset, card_setOf_resDig hπ (by omega : 0 < K) (0 : ResidueField O)]

/-- **The nonzero-constant genre**: the monic irreducible degree-`d` residue
polynomials with nonzero constant term — the digit-polynomial bank of the pinned
box (for `d ≥ 2` this is ALL of the genre). -/
def nzGenre (F : Type*) [Field F] (d : ℕ) : Set (Polynomial F) :=
  {f | (f ∈ leafGenre F d) ∧ f.coeff 0 ≠ 0}

theorem finite_nzGenre (F : Type*) [Field F] [Fintype F] (d : ℕ) :
    (nzGenre F d).Finite :=
  (finite_leafGenre F d).subset fun _ hf => hf.1

/-- The digit at the corner is the digit polynomial's constant term. -/
private theorem leafDig_zero {π : O} {m K : ℕ} (h e' d : ℕ) (c : Coeff O m K) :
    leafDig π h e' d c 0 = resDig π (h * d) (resAt c (e' * 0)) := by
  unfold leafDig
  rw [Nat.sub_zero]

/-- ★★ **THE PINNED-BOX COUNT**: `nz_d(q) · q^(e'd·K − wLeaf)` classes at every
finite level — `card_leafIrrBox`'s fiber engine over the nonzero-constant genre. -/
theorem card_pinnedBox {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) {K : ℕ} (hmK : e' * d ≤ K)
    (hhdK : h * d < K) :
    Nat.card (pinnedBox π K h e' d : Set (Coeff O (e' * d) K))
      = Nat.card (nzGenre (IsLocalRing.ResidueField O) d)
          * residueCard O ^ ((e' * d) * K - wLeaf h e' d) := by
  classical
  letI : Fintype (Coeff O (e' * d) K) := Fintype.ofFinite _
  letI : Fintype (IsLocalRing.ResidueField O) := Fintype.ofFinite _
  have he'0 : 0 < e' := by omega
  have hm0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hfin : (nzGenre (IsLocalRing.ResidueField O) d).Finite :=
    finite_nzGenre _ d
  -- the corner-membership dictionary: on the cone, corner exactness = nonzero constant digit
  have hdict : ∀ c : Coeff O (e' * d) K, c ∈ leafCone O (e' * d) K h e' →
      (resOrd (resAt c 0) = h * d ↔ (leafResPoly π h e' d c).coeff 0 ≠ 0) := by
    intro c hcone
    have hge : h * d ≤ resOrd (c ⟨0, hm0⟩) := by
      have h1 : h * (e' * d - ((⟨0, hm0⟩ : Fin (e' * d)) : ℕ))
          ≤ e' * resOrd (c ⟨0, hm0⟩) := hcone ⟨0, hm0⟩
      have h2 : h * (e' * d) ≤ e' * resOrd (c ⟨0, hm0⟩) := by simpa using h1
      have h3 : h * (e' * d) = e' * (h * d) := by ring
      rw [h3] at h2
      exact Nat.le_of_mul_le_mul_left h2 he'0
    have hcoeff : (leafResPoly π h e' d c).coeff 0 = resDig π (h * d) (resAt c 0) := by
      rw [leafResPoly_coeff_lt π h e' d c hd0, leafDig_zero, Nat.mul_zero]
    have hre : resAt c 0 = c ⟨0, hm0⟩ := resAt_lt c hm0
    rw [hcoeff, hre]
    constructor
    · intro hex
      exact ((resOrd_eq_iff_resDig hπ hhdK (c ⟨0, hm0⟩)).mp hex).2
    · intro hne
      exact (resOrd_eq_iff_resDig hπ hhdK (c ⟨0, hm0⟩)).mpr ⟨hge, hne⟩
  rw [natCard_eq_sum_fiber (pinnedBox π K h e' d)
      (fun c => leafResPoly π h e' d c) hfin.toFinset
      (fun c hc => by
        rw [Set.Finite.mem_toFinset]
        exact ⟨⟨leafResPoly_monic π h e' d c, leafResPoly_natDegree π h e' d c,
          hc.2.2⟩, (hdict c hc.1).mp hc.2.1⟩)]
  have hfib : ∀ f ∈ hfin.toFinset,
      Nat.card ((pinnedBox π K h e' d
          ∩ (fun c => leafResPoly π h e' d c) ⁻¹' {f}) : Set (Coeff O (e' * d) K))
        = residueCard O ^ ((e' * d) * K - wLeaf h e' d) := by
    intro f hf
    rw [Set.Finite.mem_toFinset] at hf
    obtain ⟨⟨hfm, hfd, hfirr⟩, hf0⟩ := hf
    have hset : pinnedBox π K h e' d
        ∩ (fun c => leafResPoly π h e' d c) ⁻¹' {f}
        = leafFiber π (e' * d) K h e' d f := by
      ext c
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      rw [mem_leafFiber_iff hπ hh hhe rfl hmK hfm hfd]
      constructor
      · rintro ⟨⟨hcone, -, -⟩, hpin⟩
        exact ⟨hcone, hpin⟩
      · rintro ⟨hcone, hpin⟩
        refine ⟨⟨hcone, ?_, by rw [hpin]; exact hfirr⟩, hpin⟩
        refine (hdict c hcone).mpr ?_
        rw [hpin]
        exact hf0
    rw [hset, card_leafFiber hπ hh hhe hd0 rfl hmK f]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]

/-- **The nonzero-constant necklace polynomial**: `X − 1` at `d = 1` (all `q`
monic linear residuals are irreducible; exactly `q − 1` avoid constant `0`),
IFCG19's `necklacePoly` for `d ≥ 2` (irreducibility already forces the nonzero
constant). -/
def nzPoly (d : ℕ) : Polynomial ℚ :=
  if d = 1 then Polynomial.X - 1 else necklacePoly d

/-- The count dictionary for the nonzero-constant genre. -/
theorem nzPoly_eval_card (F : Type*) [Field F] [Fintype F] {d : ℕ} (hd : 1 ≤ d) :
    (nzPoly d).eval ((Fintype.card F : ℕ) : ℚ) = (Nat.card (nzGenre F d) : ℚ) := by
  classical
  rcases eq_or_lt_of_le hd with hd1 | hd2
  · -- d = 1: the genre is ALL monic linears; the constraint kills exactly one constant
    subst hd1
    have hequiv : Nat.card (nzGenre F 1) = Nat.card {a : F // a ≠ 0} := by
      refine Nat.card_congr ?_
      refine ⟨fun p => ⟨p.1.coeff 0, p.2.2⟩,
        fun a => ⟨Polynomial.X + Polynomial.C a.1,
          ⟨⟨Polynomial.monic_X_add_C _, Polynomial.natDegree_X_add_C _, ?_⟩, by simp [a.2]⟩⟩,
        ?_, ?_⟩
      · exact (Polynomial.monic_X_add_C a.1).irreducible_of_degree_eq_one
          (Polynomial.degree_X_add_C a.1)
      · intro p
        obtain ⟨⟨hpm, hpd, -⟩, -⟩ := p.2
        refine Subtype.ext ?_
        have h1 : (p : Polynomial F) = Polynomial.X + Polynomial.C ((p : Polynomial F).coeff 0) := by
          have h2 := Polynomial.eq_X_add_C_of_natDegree_le_one (by omega : (p : Polynomial F).natDegree ≤ 1)
          have h3 : (p : Polynomial F).coeff 1 = 1 := by
            have h4 := hpm.coeff_natDegree
            rwa [hpd] at h4
          rw [h3, map_one, one_mul] at h2
          exact h2
        exact h1.symm
      · intro a
        refine Subtype.ext ?_
        simp
    rw [hequiv]
    have hcard : Nat.card {a : F // a ≠ 0} = Fintype.card F - 1 := by
      rw [Nat.card_eq_fintype_card]
      have h1 : Fintype.card {a : F // a ≠ 0} = Fintype.card F - 1 := by
        have h2 := Fintype.card_subtype_compl (fun a : F => a = 0)
        have h3 : Fintype.card {a : F // a = 0} = 1 := Fintype.card_subtype_eq (0 : F)
        rw [h3] at h2
        exact h2
      exact h1
    rw [hcard, nzPoly, if_pos rfl]
    have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
    have hcast : ((Fintype.card F - 1 : ℕ) : ℚ) = (Fintype.card F : ℚ) - 1 := by
      push_cast [Nat.cast_sub hq1]
      ring
    rw [hcast]
  · -- d ≥ 2: irreducibility forces the nonzero constant, the genre is the full bank
    have hne1 : d ≠ 1 := by omega
    have hset : nzGenre F d = leafGenre F d := by
      ext f
      constructor
      · exact fun hf => hf.1
      · intro hf
        refine ⟨hf, ?_⟩
        obtain ⟨-, hfd, hfirr⟩ := hf
        exact coeff_zero_ne_zero_of_irreducible hfirr (by omega)
    have hcard : Nat.card (nzGenre F d) = Nat.card (IrredOfDeg F d) := by
      rw [hset]
      rfl
    rw [hcard, nzPoly, if_neg hne1, necklacePoly_eval_card F d hd]

end Carriers

/-! ## §2 — THE PRODUCT PACKAGE, part 1: the coefficient data and the face data of
(pinned box) × (steep linear) -/

section ProductData

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The threshold ladder: `tLeaf` at consecutive abscissae rises by at most one. -/
private theorem tLeaf_succ_le {h e' : ℕ} (hh : 0 < h) (hhe : h < e') (n i : ℕ) :
    tLeaf h e' n i ≤ tLeaf h e' n (i + 1) + 1 := by
  have he'0 : 0 < e' := by omega
  refine (tLeaf_le_iff he'0 h n i _).mpr ?_
  have h1 : h * (n - (i + 1)) ≤ e' * tLeaf h e' n (i + 1) :=
    (tLeaf_le_iff he'0 h n (i + 1) _).mp le_rfl
  have h2 : e' * (tLeaf h e' n (i + 1) + 1) = e' * tLeaf h e' n (i + 1) + e' := by ring
  have h3 : h * (n - i) ≤ h * (n - (i + 1)) + h := by
    by_cases hni : n ≤ i
    · rw [Nat.sub_eq_zero_of_le hni, Nat.sub_eq_zero_of_le (by omega)]
      omega
    · have h4 : n - i = (n - (i + 1)) + 1 := by omega
      rw [h4, Nat.mul_add, Nat.mul_one]
  omega

/-- The corner threshold at the r = 1 total mass: `tLeaf (e'd + 1) 0 = h·d + 1`. -/
private theorem tLeaf_r_one_zero {h e' d : ℕ} (hh : 0 < h) (hhe : h < e') :
    tLeaf h e' (e' * d + 1) 0 = h * d + 1 := by
  have he'0 : 0 < e' := by omega
  unfold tLeaf
  rw [Nat.sub_zero]
  have h1 : h * (e' * d + 1) = e' * (h * d) + h := by ring
  have h2 : h * (e' * d + 1) + (e' - 1) = e' * (h * d + 1) + (h - 1) := by
    have h3 : e' * (h * d + 1) = e' * (h * d) + e' := by ring
    omega
  rw [h2, Nat.mul_add_div he'0, Nat.div_eq_of_lt (by omega : h - 1 < e'), Nat.add_zero]

/-- The shifted thresholds agree: `tLeaf (e'd + 1) (i+1) = tLeaf (e'd) i`. -/
private theorem tLeaf_r_one_succ (h e' d i : ℕ) :
    tLeaf h e' (e' * d + 1) (i + 1) = tLeaf h e' (e' * d) i := by
  unfold tLeaf
  have h1 : e' * d + 1 - (i + 1) = e' * d - i := by omega
  rw [h1]

/-- The thresholds are antitone in the abscissa. -/
private theorem tLeaf_antitone (h e' m : ℕ) {i j : ℕ} (hij : i ≤ j) :
    tLeaf h e' m j ≤ tLeaf h e' m i := by
  unfold tLeaf
  exact Nat.div_le_div_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left h (by omega)) _)

/-- The abscissa-1 threshold on the block dominates the corner: `h·d ≤ tLeaf (e'd) 1`. -/
private theorem hd_le_tLeaf_one {h e' d : ℕ} (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) :
    h * d ≤ tLeaf h e' (e' * d) 1 := by
  have he'0 : 0 < e' := by omega
  have hn1 : 1 ≤ e' * d := Nat.mul_pos he'0 hd0
  have h1 : h * (e' * d - 1) ≤ e' * tLeaf h e' (e' * d) 1 :=
    (tLeaf_le_iff he'0 h (e' * d) 1 _).mp le_rfl
  have h2 : h * (e' * d - 1) + h = h * (e' * d) := by
    have h3 : e' * d - 1 + 1 = e' * d := by omega
    calc h * (e' * d - 1) + h = h * ((e' * d - 1) + 1) := by ring
      _ = h * (e' * d) := by rw [h3]
  have h4 : h * (e' * d) = e' * (h * d) := by ring
  have h5 : e' * (h * d) < e' * (tLeaf h e' (e' * d) 1 + 1) := by
    have h6 : e' * (tLeaf h e' (e' * d) 1 + 1) = e' * tLeaf h e' (e' * d) 1 + e' := by ring
    omega
  have h7 : h * d < tLeaf h e' (e' * d) 1 + 1 := Nat.lt_of_mul_lt_mul_left h5
  omega

/-- **The product coefficient data at r = 1**: the class of `g·(X + α)` — `g` a
cone-with-exact-corner block, `α` in the maximal ideal — carries the frame cone at
total mass `e'd + 1` with the EXACT coordinate `resOrd = h·d` at abscissa `1` and
the strictly-raised corner `resOrd ≥ h·d + 1` at abscissa `0`. -/
private theorem prod_class_data {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) {K : ℕ} (hhdK : h * d + 1 ≤ K)
    {a₁ : Fin (e' * d) → O} {a₂ : Fin 1 → O}
    (hcone : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) K a₁ j))
    (hcorner : resOrd (resAt (proj O (e' * d) K a₁) 0) = h * d)
    (hsteep : 1 ≤ resOrd (proj O 1 K a₂ 0)) :
    (∀ j : Fin (e' * d + 1),
        h * ((e' * d + 1) - (j : ℕ))
          ≤ e' * resOrd (proj O (e' * d + 1) K
              (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) j))
      ∧ resOrd (resAt (proj O (e' * d + 1) K
          (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) 1) = h * d
      ∧ h * d + 1 ≤ resOrd (resAt (proj O (e' * d + 1) K
          (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) 0) := by
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hn2 : 2 ≤ e' * d := by
    have h1 : 2 ≤ e' := by omega
    have h2 : e' * 1 ≤ e' * d := Nat.mul_le_mul_left e' hd0
    omega
  -- the lift-side divisibilities
  have hre : resAt (proj O (e' * d) K a₁) 0 = proj O (e' * d) K a₁ ⟨0, hn0⟩ :=
    resAt_lt _ hn0
  rw [hre] at hcorner
  have hvis0 : classCoeffVal (proj O (e' * d) K a₁) ⟨0, hn0⟩ < K := by
    show resOrd (proj O (e' * d) K a₁ ⟨0, hn0⟩) < K
    omega
  have hL1 := classCoeffVal_exact hπ rfl hvis0
  rw [show classCoeffVal (proj O (e' * d) K a₁) ⟨0, hn0⟩ = h * d from hcorner] at hL1
  have hL2 : ∀ j : Fin (e' * d), π ^ (tLeaf h e' (e' * d) (j : ℕ)) ∣ a₁ j := by
    intro j
    have h1 : tLeaf h e' (e' * d) (j : ℕ) ≤ resOrd (proj O (e' * d) K a₁ j) :=
      (tLeaf_le_iff he'0 h (e' * d) (j : ℕ) _).mpr (hcone j)
    have h2 : π ^ (resOrd (proj O (e' * d) K a₁ j)) ∣ a₁ j :=
      (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
    exact (pow_dvd_pow π h1).trans h2
  have hL3 : π ∣ a₂ 0 := by
    have h2 : π ^ 1 ∣ a₂ 0 :=
      (le_classCoeffVal_iff_dvd hπ (by omega : 1 ≤ K) rfl 0).mp hsteep
    rwa [pow_one] at h2
  -- the product coefficient identities
  have hsplit : monicPoly a₁ * monicPoly a₂
      = monicPoly a₁ * Polynomial.X + Polynomial.C (a₂ 0) * monicPoly a₁ := by
    rw [monicPoly_one_eq a₂]
    ring
  have hPc0 : (monicPoly a₁ * monicPoly a₂).coeff 0 = a₂ 0 * a₁ ⟨0, hn0⟩ := by
    rw [hsplit, Polynomial.coeff_add, Polynomial.coeff_mul_X_zero,
      Polynomial.coeff_C_mul, monicPoly_coeff_lt a₁ hn0, zero_add]
  have hPcS : ∀ (i : ℕ) (hi : i < e' * d),
      (monicPoly a₁ * monicPoly a₂).coeff (i + 1)
        = a₁ ⟨i, hi⟩ + a₂ 0 * (monicPoly a₁).coeff (i + 1) := by
    intro i hi
    rw [hsplit, Polynomial.coeff_add, Polynomial.coeff_mul_X,
      Polynomial.coeff_C_mul, monicPoly_coeff_lt a₁ hi]
  -- the divisibility bank on the product coefficients
  have hdvdP : ∀ j : Fin (e' * d + 1),
      π ^ (tLeaf h e' (e' * d + 1) (j : ℕ))
        ∣ (monicPoly a₁ * monicPoly a₂).coeff (j : ℕ) := by
    rintro ⟨j, hj⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · show π ^ (tLeaf h e' (e' * d + 1) 0) ∣ _
      rw [tLeaf_r_one_zero hh hhe, hPc0, pow_succ']
      exact mul_dvd_mul hL3 hL1.1
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj0)
      have hi : i < e' * d := by omega
      show π ^ (tLeaf h e' (e' * d + 1) (i + 1)) ∣ _
      rw [tLeaf_r_one_succ, hPcS i hi]
      refine dvd_add (hL2 ⟨i, hi⟩) ?_
      rcases Nat.lt_or_ge (i + 1) (e' * d) with hi1 | hi1
      · -- the interior term: `α · a₁ (i+1)` at threshold `1 + tLeaf (i+1)`
        rw [monicPoly_coeff_lt a₁ hi1]
        have h1 : π ^ (tLeaf h e' (e' * d) (i + 1) + 1)
            ∣ a₂ 0 * a₁ ⟨i + 1, hi1⟩ := by
          rw [pow_succ, mul_comm (π ^ _) π]
          exact mul_dvd_mul hL3 (hL2 ⟨i + 1, hi1⟩)
        exact (pow_dvd_pow π (tLeaf_succ_le hh hhe (e' * d) i)).trans h1
      · -- the top term: `α · 1` at threshold `tLeaf (e'd − 1) ≤ 1`
        have hieq : i + 1 = e' * d := by omega
        have htop : (monicPoly a₁).coeff (i + 1) = 1 := by
          rw [hieq]
          have h1 := (monicPoly_monic a₁).coeff_natDegree
          rwa [monicPoly_natDegree] at h1
        rw [htop, mul_one]
        have h2 : tLeaf h e' (e' * d) i ≤ 1 := by
          refine (tLeaf_le_iff he'0 h (e' * d) i 1).mpr ?_
          have h3 : e' * d - i = 1 := by omega
          rw [h3, Nat.mul_one, Nat.mul_one]
          omega
        exact (pow_dvd_pow π h2).trans (by rwa [pow_one])
  -- the threshold cap: `tLeaf (m, j) ≤ h·d + 1 ≤ K`
  have hcap : ∀ j : ℕ, tLeaf h e' (e' * d + 1) j ≤ h * d + 1 := by
    intro j
    have h1 := tLeaf_antitone h e' (e' * d + 1) (Nat.zero_le j)
    rw [tLeaf_r_one_zero hh hhe] at h1
    exact h1
  -- CONE
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have h1 : tLeaf h e' (e' * d + 1) (j : ℕ)
        ≤ resOrd (proj O (e' * d + 1) K
            (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) j) :=
      (le_classCoeffVal_iff_dvd hπ (le_trans (hcap _) hhdK) rfl j).mpr (hdvdP j)
    have h2 : h * ((e' * d + 1) - (j : ℕ)) ≤ e' * tLeaf h e' (e' * d + 1) (j : ℕ) :=
      (tLeaf_le_iff he'0 h (e' * d + 1) (j : ℕ) _).mp le_rfl
    have h3 : e' * tLeaf h e' (e' * d + 1) (j : ℕ)
        ≤ e' * resOrd (proj O (e' * d + 1) K
            (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) j) :=
      Nat.mul_le_mul_left e' h1
    omega
  · -- the EXACT coordinate at abscissa 1
    have h1m : (1 : ℕ) < e' * d + 1 := by omega
    rw [resAt_lt _ h1m]
    show resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ K)
      ((monicPoly a₁ * monicPoly a₂).coeff ((⟨1, h1m⟩ : Fin (e' * d + 1)) : ℕ))) = h * d
    have hc1 : (monicPoly a₁ * monicPoly a₂).coeff 1
        = a₁ ⟨0, hn0⟩ + a₂ 0 * (monicPoly a₁).coeff 1 := hPcS 0 hn0
    have hc1' : (monicPoly a₁).coeff 1 = a₁ ⟨1, by omega⟩ :=
      monicPoly_coeff_lt a₁ (by omega)
    have hterm2 : π ^ (h * d + 1) ∣ a₂ 0 * (monicPoly a₁).coeff 1 := by
      rw [hc1']
      have h1 : π ^ (tLeaf h e' (e' * d) 1 + 1) ∣ a₂ 0 * a₁ ⟨1, by omega⟩ := by
        rw [pow_succ, mul_comm (π ^ _) π]
        exact mul_dvd_mul hL3 (hL2 ⟨1, by omega⟩)
      exact (pow_dvd_pow π (by
        have := hd_le_tLeaf_one hh hhe hd0
        omega)).trans h1
    refine resOrd_mk_eq hπ (by omega) ?_ (Or.inr ?_)
    · rw [hc1]
      exact dvd_add hL1.1 ((pow_dvd_pow π (by omega)).trans hterm2)
    · intro hcon
      rw [hc1] at hcon
      refine hL1.2 ?_
      have h2 := dvd_sub hcon hterm2
      rwa [add_sub_cancel_right] at h2
  · -- the strictly-raised corner
    have h0m : (0 : ℕ) < e' * d + 1 := by omega
    rw [resAt_lt _ h0m]
    refine (le_classCoeffVal_iff_dvd hπ hhdK rfl ⟨0, h0m⟩).mpr ?_
    show π ^ (h * d + 1) ∣ (monicPoly a₁ * monicPoly a₂).coeff 0
    rw [hPc0, pow_succ']
    exact mul_dvd_mul hL3 hL1.1

/-- **The face package**: a mass-`(e'd + 1)` class carrying the frame cone with the
exact abscissa-1 coordinate and the raised corner has minimal face `(h, e')` NOT
attained at `0`, lies in the `X^m`-stratum and the shallow set, and avoids every
integer-slope pure-face box. -/
private theorem face_package {h e' d : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d)
    {K : ℕ} (hmK : e' * d + 1 ≤ K) {c : Coeff O (e' * d + 1) K}
    (hcone : ∀ j : Fin (e' * d + 1),
      h * ((e' * d + 1) - (j : ℕ)) ≤ e' * resOrd (c j))
    (hone : resOrd (resAt c 1) = h * d)
    (hzero : h * d + 1 ≤ resOrd (resAt c 0)) :
    MinFaceAt c h e' ∧ ¬ NPAttains c h e' 0
      ∧ c ∈ levelZeroStratum O (e' * d + 1) K (Polynomial.X ^ (e' * d + 1))
      ∧ c ∈ shallowSet O (e' * d + 1) K
      ∧ c ∉ pureFaceSet O (e' * d + 1) K := by
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have h0m : (0 : ℕ) < e' * d + 1 := by omega
  have h1m : (1 : ℕ) < e' * d + 1 := by omega
  have hre0 : resAt c 0 = c ⟨0, h0m⟩ := resAt_lt c h0m
  have hre1 : resAt c 1 = c ⟨1, h1m⟩ := resAt_lt c h1m
  rw [hre0] at hzero
  rw [hre1] at hone
  have hnp0 : npHeight c 0 = resOrd (c ⟨0, h0m⟩) := by
    have h5 := npHeight_coe c ⟨0, h0m⟩
    simpa using h5
  have hnp1 : npHeight c 1 = resOrd (c ⟨1, h1m⟩) := by
    have h5 := npHeight_coe c ⟨1, h1m⟩
    simpa using h5
  have hnpm : npHeight c (e' * d + 1) = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl (e' * d + 1))]
  -- the support is `h·m`, attained at `1` and `m`, missed at `0`
  have hsup : classNPSupport c h e' = h * (e' * d + 1) := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h2 := classNPSupport_le_apply c h e' (by omega : 1 ≤ e' * d + 1)
      rw [hnp1, hone] at h2
      have h3 : e' * (h * d) + h * 1 = h * (e' * d + 1) := by ring
      omega
    · intro i hi
      rcases eq_or_lt_of_le hi with heq | hilt
      · subst heq
        rw [hnpm]
        omega
      · have hf : h * ((e' * d + 1) - i) ≤ e' * resOrd (c ⟨i, hilt⟩) := by
          simpa using hcone ⟨i, hilt⟩
        have hnp : npHeight c i = resOrd (c ⟨i, hilt⟩) := by
          have h5 := npHeight_coe c ⟨i, hilt⟩
          simpa using h5
        rw [hnp]
        have hdist : h * ((e' * d + 1) - i) + h * i = h * (e' * d + 1) := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hilt)]
        omega
  have hA1 : NPAttains c h e' 1 := by
    refine ⟨by omega, ?_⟩
    rw [hnp1, hone, hsup]
    ring
  have hAm : NPAttains c h e' (e' * d + 1) := by
    refine ⟨le_refl _, ?_⟩
    rw [hnpm, hsup]
    ring
  have hnA0 : ¬ NPAttains c h e' 0 := by
    rintro ⟨-, h2⟩
    rw [hnp0, hsup, Nat.mul_zero, Nat.add_zero] at h2
    have h3 : e' * (h * d + 1) ≤ e' * resOrd (c ⟨0, h0m⟩) :=
      Nat.mul_le_mul_left e' hzero
    have h4 : e' * (h * d + 1) = e' * (h * d) + e' := by ring
    have h5 : h * (e' * d + 1) = e' * (h * d) + h := by ring
    omega
  have hvis : NPVisibleAt c h e' := by
    show classNPSupport c h e' < e' * K
    rw [hsup]
    have h1 : h * (e' * d + 1) < e' * (e' * d + 1) := by
      have := (Nat.mul_lt_mul_right (show 0 < e' * d + 1 by omega)).mpr hhe
      omega
    have h2 : e' * (e' * d + 1) ≤ e' * K := Nat.mul_le_mul_left e' hmK
    omega
  have hF : MinFaceAt c h e' :=
    ⟨hh1, hhe, hcop, ⟨1, e' * d + 1, by omega, hA1, hAm⟩, hAm, hvis⟩
  -- the stratum
  have hstr : c ∈ levelZeroStratum O (e' * d + 1) K (Polynomial.X ^ (e' * d + 1)) := by
    refine (mem_stratum_X_pow_iff (by omega : 1 ≤ K) c).2 fun i => ?_
    have h1 := hcone i
    have h2 : 0 < h * ((e' * d + 1) - (i : ℕ)) :=
      Nat.mul_pos (by omega) (by have := i.isLt; omega)
    rcases Nat.eq_zero_or_pos (resOrd (c i)) with h3 | h3
    · rw [h3, Nat.mul_zero] at h1
      omega
    · exact h3
  -- shallow: the exact coordinate at `1` dips below its Eisenstein corner
  have hsh : c ∈ shallowSet O (e' * d + 1) K := by
    refine ⟨⟨1, h1m⟩, ?_⟩
    show resOrd (c ⟨1, h1m⟩) < (e' * d + 1) - 1
    rw [hone]
    have h1 : h * d < e' * d := by
      have := (Nat.mul_lt_mul_right hd0).mpr hhe
      omega
    omega
  -- not in any integer-slope pure-face box
  have hnp : c ∉ pureFaceSet O (e' * d + 1) K := by
    rintro ⟨h'', hmem'', hb1, hb2⟩
    have hb1' : h'' = resOrd (c ⟨0, h0m⟩) := by rw [← hnp0, hb1]
    have hge : h * d + 1 ≤ h'' := by omega
    have hat1 := hb2 ⟨1, h1m⟩
    have hnp1' : npHeight c ((⟨1, h1m⟩ : Fin (e' * d + 1)) : ℕ) = h * d := by
      rw [show ((⟨1, h1m⟩ : Fin (e' * d + 1)) : ℕ) = 1 from rfl, hnp1, hone]
    rw [hnp1'] at hat1
    have hsub : (e' * d + 1) - ((⟨1, h1m⟩ : Fin (e' * d + 1)) : ℕ) = e' * d := by
      show (e' * d + 1) - 1 = e' * d
      omega
    rw [hsub] at hat1
    have hmul : (h * d + 1) * (e' * d) ≤ h'' * (e' * d) :=
      Nat.mul_le_mul_right _ hge
    have e1 : (h * d + 1) * (e' * d) = h * d * (e' * d) + e' * d := by ring
    have e2 : (e' * d + 1) * (h * d) = e' * d * (h * d) + h * d := by ring
    have e3 : h * d * (e' * d) = e' * d * (h * d) := by ring
    have h1 : h * d < e' * d := by
      have := (Nat.mul_lt_mul_right hd0).mpr hhe
      omega
    omega
  exact ⟨hF, hnA0, hstr, hsh, hnp⟩

end ProductData

/-! ## §3 — THE PRODUCT RESIDUAL: `classResidualPoly (γ·ρ) = classResidualPoly γ · unit`
(the linear factor's side residual is a nonzero constant) -/

section ProductResidual

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The residual factorization at r = 1**: the canonical residual of the product
class is the block's residual times a UNIT, with both degrees pinned to `d`.  This
carries the digit-polynomial irreducibility in BOTH directions between the box and
the cell. -/
private theorem prod_residual {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d)
    {K : ℕ} (hmK : e' * d + 1 ≤ K) (hhdK : h * d + 1 ≤ K)
    {a₁ : Fin (e' * d) → O} {a₂ : Fin 1 → O}
    (hcone : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) K a₁ j))
    (hcorner : resOrd (resAt (proj O (e' * d) K a₁) 0) = h * d)
    (hsteep : 1 ≤ resOrd (proj O 1 K a₂ 0)) :
    ∃ u : Polynomial (resField (X : Polynomial O)), IsUnit u
      ∧ classResidualPoly π (proj O (e' * d + 1) K
          (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e'
        = classResidualPoly π (proj O (e' * d) K a₁) h e' * u
      ∧ (classResidualPoly π (proj O (e' * d) K a₁) h e').natDegree = d
      ∧ (classResidualPoly π (proj O (e' * d + 1) K
          (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e').natDegree = d := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  -- the block's class face data at its own mass
  have hcorner' : resOrd (proj O (e' * d) K a₁ ⟨0, hn0⟩) = h * d := by
    rw [← resAt_lt (proj O (e' * d) K a₁) hn0]
    exact hcorner
  obtain ⟨hsupγ, hA0γ, hAmγ, hvisγ⟩ :=
    leafCone_face_data hh hhe hd0 rfl hn0 (by omega : e' * d ≤ K) hcone hcorner'
  -- the steep linear factor's class face data at mass 1
  have hnpρ1 : npHeight (proj O 1 K a₂) 1 = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl 1)]
  have hnpρ0 : npHeight (proj O 1 K a₂) 0 = resOrd (proj O 1 K a₂ 0) := by
    have h5 := npHeight_coe (proj O 1 K a₂) 0
    simpa using h5
  have hsupρ : classNPSupport (proj O 1 K a₂) h e' = h := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h2 := classNPSupport_le_apply (proj O 1 K a₂) h e' (le_refl 1)
      rw [hnpρ1] at h2
      omega
    · intro i hi
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
      · rw [hnpρ0]
        have h3 : e' * 1 ≤ e' * resOrd (proj O 1 K a₂ 0) :=
          Nat.mul_le_mul_left e' hsteep
        omega
      · rw [hnpρ1]
        omega
  have hA1ρ : NPAttains (proj O 1 K a₂) h e' 1 := by
    refine ⟨le_refl 1, ?_⟩
    rw [hnpρ1, hsupρ]
    ring
  have hnA0ρ : ¬ NPAttains (proj O 1 K a₂) h e' 0 := by
    rintro ⟨-, hc⟩
    rw [hnpρ0, hsupρ, Nat.mul_zero, Nat.add_zero] at hc
    have h3 : e' * 1 ≤ e' * resOrd (proj O 1 K a₂ 0) :=
      Nat.mul_le_mul_left e' hsteep
    omega
  have hvisρ : NPVisibleAt (proj O 1 K a₂) h e' := by
    show classNPSupport (proj O 1 K a₂) h e' < e' * K
    rw [hsupρ]
    have h3 : e' * 1 ≤ e' * K := Nat.mul_le_mul_left e' (by omega)
    omega
  have hclassρ : classSideSet (proj O 1 K a₂) h e' = {1} := by
    ext j
    rw [mem_classSideSet_iff', Finset.mem_singleton]
    constructor
    · rintro ⟨hj2, hAt⟩
      have hj01 : j = 0 ∨ j = 1 := by omega
      rcases hj01 with rfl | rfl
      · exact absurd hAt hnA0ρ
      · rfl
    · rintro rfl
      exact ⟨by omega, hA1ρ⟩
  -- the block's lift-side side data
  have hnf : (sideSet X (monicPoly a₁) h e').Nonempty := sideSet_nonempty_gen _ _ _ _
  have h0memγ : (0 : ℕ) ∈ classSideSet (proj O (e' * d) K a₁) h e' :=
    mem_classSideSet_iff'.mpr ⟨by omega, hA0γ⟩
  have hcneγ : (classSideSet (proj O (e' * d) K a₁) h e').Nonempty := ⟨0, h0memγ⟩
  have hming : sideMin X (monicPoly a₁) h e' hnf = 0 := by
    rw [sideMin_monicPoly_eq hπ he'0 hvisγ rfl hnf hcneγ]
    exact Nat.le_zero.mp (Finset.min'_le _ 0 h0memγ)
  have hvis0γ : classCoeffVal (proj O (e' * d) K a₁) ⟨0, hn0⟩ < K := by
    show resOrd (proj O (e' * d) K a₁ ⟨0, hn0⟩) < K
    omega
  have hHg' : npHgt X (monicPoly a₁) (sideMin X (monicPoly a₁) h e' hnf)
      = ((h * d : ℕ) : ℕ∞) := by
    rw [hming]
    have h1 := npHgt_monicPoly_eq hπ
      (rfl : proj O (e' * d) K a₁ = proj O (e' * d) K a₁) hn0 hvis0γ
    rw [h1, show classCoeffVal (proj O (e' * d) K a₁) ⟨0, hn0⟩ = h * d from hcorner']
  -- the steep factor's lift-side side data
  have hnz : (sideSet X (monicPoly a₂) h e').Nonempty := sideSet_nonempty_gen _ _ _ _
  have hsetR : sideSet X (monicPoly a₂) h e' = {1} := by
    rw [sideSet_monicPoly_eq hπ he'0 hvisρ rfl]
    exact hclassρ
  have hminR : sideMin X (monicPoly a₂) h e' hnz = 1 := by
    refine le_antisymm
      (Finset.min'_le _ 1 (by rw [hsetR]; exact Finset.mem_singleton_self 1)) ?_
    refine Finset.le_min' _ _ _ fun y hy => ?_
    rw [hsetR, Finset.mem_singleton] at hy
    omega
  have hmaxR : sideMax X (monicPoly a₂) h e' hnz = 1 := by
    refine le_antisymm ?_
      (Finset.le_max' _ 1 (by rw [hsetR]; exact Finset.mem_singleton_self 1))
    refine Finset.max'_le _ _ _ fun y hy => ?_
    rw [hsetR, Finset.mem_singleton] at hy
    omega
  have hHR' : npHgt X (monicPoly a₂) (sideMin X (monicPoly a₂) h e' hnz)
      = ((0 : ℕ) : ℕ∞) := by
    rw [hminR]
    have h1 := npHgt_monic_top (monicPoly_monic a₂)
    rw [monicPoly_natDegree] at h1
    simpa using h1
  have htg : suppVal X (monicPoly a₁) h e' ≠ ⊤ :=
    suppVal_ne_top_of_monic (monicPoly_monic a₁) h e'
  have htR : suppVal X (monicPoly a₂) h e' ≠ ⊤ :=
    suppVal_ne_top_of_monic (monicPoly_monic a₂) h e'
  -- the product's lift-side side data (B.39a §7)
  have hnfz : (sideSet X (monicPoly a₁ * monicPoly a₂) h e').Nonempty :=
    sideSet_nonempty_gen _ _ _ _
  have hminmul := sideMin_mul_gen hπ isKey_X hh he'0 hcop htg htR hnf hnz hHg' hHR' hnfz
  have hnpmul := npHgt_mul_gen hπ isKey_X hh he'0 hcop htg htR hnf hnz hHg' hHR'
  have hrpmul := resPoly_mul_gen hπ isKey_X hh he'0 hcop htg htR hnf hnz hHg' hHR' hnfz
  -- the block's residual and its degree (the bridge)
  have hcrpγ : classResidualPoly π (proj O (e' * d) K a₁) h e'
      = resPoly π X (monicPoly a₁) h e' hnf (h * d) :=
    classResidualPoly_eq hπ he'0 hvisγ rfl hnf hHg'
  have hbridge := classResidualPoly_eq_leafResPoly hπ hh hhe hd0 rfl hn0
    (by omega : e' * d ≤ K) hcone hcorner'
  have hdegγ : (classResidualPoly π (proj O (e' * d) K a₁) h e').natDegree = d := by
    rw [hbridge, (leafResPoly_monic π h e' d _).natDegree_map]
    exact leafResPoly_natDegree π h e' d _
  -- the product's frame polynomial IS the product
  have hPm : (monicPoly a₁ * monicPoly a₂).Monic :=
    (monicPoly_monic a₁).mul (monicPoly_monic a₂)
  have hPdeg : (monicPoly a₁ * monicPoly a₂).natDegree = e' * d + 1 := by
    rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂),
      monicPoly_natDegree, monicPoly_natDegree]
  have hmp : monicPoly (fun i : Fin (e' * d + 1) =>
      (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) = monicPoly a₁ * monicPoly a₂ :=
    monicPoly_coeff_eq_self hPm hPdeg
  -- the product class's visibility (through the face package)
  obtain ⟨hconeP, honeP, hzeroP⟩ :=
    prod_class_data hπ hh hhe hd0 hhdK hcone hcorner hsteep
  obtain ⟨hFP, -, -, -, -⟩ :=
    face_package (by omega) hhe hcop hd0 hmK hconeP honeP hzeroP
  have hvisP : NPVisibleAt (proj O (e' * d + 1) K
      (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e' := hFP.2.2.2.2.2
  -- the H-data on the product frame
  have hne_c : (sideSet X (monicPoly (fun i : Fin (e' * d + 1) =>
      (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e').Nonempty :=
    sideSet_nonempty_gen _ _ _ _
  have hnp01 : npHgt X (monicPoly a₁ * monicPoly a₂) (0 + 1)
      = ((h * d + 0 : ℕ) : ℕ∞) := by
    have h2 := hnpmul
    rw [hming, hminR] at h2
    exact h2
  have hH_c : npHgt X (monicPoly (fun i : Fin (e' * d + 1) =>
      (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)))
      (sideMin X (monicPoly (fun i : Fin (e' * d + 1) =>
        (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e' hne_c)
      = ((h * d + 0 : ℕ) : ℕ∞) := by
    have h1 : sideMin X (monicPoly (fun i : Fin (e' * d + 1) =>
        (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e' hne_c = 0 + 1 := by
      rw [sideMin_congr hmp hne_c hnfz, hminmul, hming, hminR]
    rw [h1, hmp]
    exact hnp01
  -- the product's residual factors
  have hcrpP : classResidualPoly π (proj O (e' * d + 1) K
      (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e'
      = resPoly π X (monicPoly (fun i : Fin (e' * d + 1) =>
          (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e' hne_c (h * d + 0) :=
    classResidualPoly_eq hπ he'0 hvisP rfl hne_c hH_c
  have hrescP : classResidualPoly π (proj O (e' * d + 1) K
      (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e'
      = resPoly π X (monicPoly a₁) h e' hnf (h * d)
        * resPoly π X (monicPoly a₂) h e' hnz 0 := by
    rw [hcrpP, resPoly_congr hmp hne_c hnfz, hrpmul]
  -- the steep factor's residual is a UNIT (degree 0, nonzero constant)
  have hRdata := natDegree_resPoly hπ isKey_X he'0 hcop htR hnz hHR'
  have hsdR : sideDeg X (monicPoly a₂) h e' hnz = 0 := by
    unfold sideDeg
    rw [hmaxR, hminR]
    simp
  have huR : IsUnit (resPoly π X (monicPoly a₂) h e' hnz 0) := by
    have hdeg0 : (resPoly π X (monicPoly a₂) h e' hnz 0).natDegree = 0 := by
      rw [hRdata.1, hsdR]
    have hne0 : (resPoly π X (monicPoly a₂) h e' hnz 0).coeff 0 ≠ 0 := hRdata.2
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by
      rwa [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, Polynomial.coeff_C_zero] at hne0))
  have hdegg : (resPoly π X (monicPoly a₁) h e' hnf (h * d)).natDegree = d := by
    rw [← hcrpγ]
    exact hdegγ
  have hgne : resPoly π X (monicPoly a₁) h e' hnf (h * d) ≠ 0 := by
    intro h0
    have h1 := (natDegree_resPoly hπ isKey_X he'0 hcop htg hnf hHg').2
    rw [h0] at h1
    simp at h1
  refine ⟨resPoly π X (monicPoly a₂) h e' hnz 0, huR, ?_, hdegγ, ?_⟩
  · rw [hrescP, hcrpγ]
  · rw [hrescP, Polynomial.natDegree_mul hgne huR.ne_zero, hdegg,
      Polynomial.natDegree_eq_zero_of_isUnit huR]
    omega

end ProductResidual

/-! ## §4 — THE DECIDEDNESS LEGS AND THE IMAGE: (pinned box) × (steep linear)
lands in `subfaceCell` -/

section Image

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **Every mass-1 class is decided `⟨{(1,1)}⟩`** at every level — the r = 1
drainage leg, outright (`typeOf_of_natDegree_one`). -/
theorem decidedAt_linear {K : ℕ} (c : Coeff O 1 K) :
    DecidedAt O 1 ⟨{(1, 1)}⟩ K c := by
  intro b _
  exact typeOf_of_natDegree_one (monicPoly_monic b) (monicPoly_natDegree b)

/-- **The box decision at the shifted window**: the pinned-box data truncates from
window `K` to `K − h·d` (every box read lives at digit levels `≤ h·d`), so IFCG37's
spanning decision fires there — the r = 1 box drainage leg, outright. -/
private theorem box_decided_shifted {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d)
    {K : ℕ} (hK2 : 2 * (h * d) < K) (hKm : e' * d + h * d ≤ K)
    {a₁ : Fin (e' * d) → O}
    (hcone : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) K a₁ j))
    (hcorner : resOrd (resAt (proj O (e' * d) K a₁) 0) = h * d)
    (hirr : Irreducible (leafResPoly π h e' d (proj O (e' * d) K a₁))) :
    DecidedAt O (e' * d) ⟨{(e', d)}⟩ (K - h * d) (proj O (e' * d) (K - h * d) a₁) := by
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hdK' : h * d < K - h * d := by omega
  have hnK' : e' * d ≤ K - h * d := by omega
  -- the lift-side data extracted at the wide window
  have hcorner' : resOrd (proj O (e' * d) K a₁ ⟨0, hn0⟩) = h * d := by
    rw [← resAt_lt (proj O (e' * d) K a₁) hn0]
    exact hcorner
  have hvis0 : classCoeffVal (proj O (e' * d) K a₁) ⟨0, hn0⟩ < K := by
    show resOrd (proj O (e' * d) K a₁ ⟨0, hn0⟩) < K
    omega
  have hL1 := classCoeffVal_exact hπ rfl hvis0
  rw [show classCoeffVal (proj O (e' * d) K a₁) ⟨0, hn0⟩ = h * d from hcorner'] at hL1
  have hL2 : ∀ j : Fin (e' * d), π ^ (tLeaf h e' (e' * d) (j : ℕ)) ∣ a₁ j := by
    intro j
    have h1 : tLeaf h e' (e' * d) (j : ℕ) ≤ resOrd (proj O (e' * d) K a₁ j) :=
      (tLeaf_le_iff he'0 h (e' * d) (j : ℕ) _).mpr (hcone j)
    have h2 : π ^ (resOrd (proj O (e' * d) K a₁ j)) ∣ a₁ j :=
      (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
    exact (pow_dvd_pow π h1).trans h2
  -- the cone at the shifted window
  have hcone' : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) (K - h * d) a₁ j) := by
    intro j
    have hcap : tLeaf h e' (e' * d) (j : ℕ) ≤ h * d := tLeaf_le_corner he'0 h d _
    have h1 : tLeaf h e' (e' * d) (j : ℕ)
        ≤ resOrd (proj O (e' * d) (K - h * d) a₁ j) :=
      (le_classCoeffVal_iff_dvd hπ (by omega) rfl j).mpr (hL2 j)
    have h2 : h * (e' * d - (j : ℕ)) ≤ e' * tLeaf h e' (e' * d) (j : ℕ) :=
      (tLeaf_le_iff he'0 h (e' * d) (j : ℕ) _).mp le_rfl
    have h3 : e' * tLeaf h e' (e' * d) (j : ℕ)
        ≤ e' * resOrd (proj O (e' * d) (K - h * d) a₁ j) :=
      Nat.mul_le_mul_left e' h1
    omega
  -- the exact corner at the shifted window
  have hcorner'' : resOrd (proj O (e' * d) (K - h * d) a₁ ⟨0, hn0⟩) = h * d := by
    show resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ (K - h * d)) (a₁ ⟨0, hn0⟩)) = h * d
    exact resOrd_mk_eq hπ (by omega) hL1.1 (Or.inr hL1.2)
  -- the digit polynomial survives the shift
  have hdig : leafResPoly π h e' d (proj O (e' * d) (K - h * d) a₁)
      = leafResPoly π h e' d (proj O (e' * d) K a₁) := by
    refine (leafResPoly_eq_iff π h e' d _ (leafResPoly_monic π h e' d _)
      (leafResPoly_natDegree π h e' d _)).mpr fun k hk => ?_
    have hek : e' * k < e' * d := by
      have h1 : e' * (k + 1) ≤ e' * d := Nat.mul_le_mul_left e' (by omega)
      have h2 : e' * (k + 1) = e' * k + e' := by ring
      omega
    have hlev : h * (d - k) ≤ h * d := Nat.mul_le_mul_left h (Nat.sub_le _ _)
    rw [leafResPoly_coeff_lt π h e' d _ hk]
    unfold leafDig
    rw [resAt_lt _ hek, resAt_lt _ hek]
    show resDig π (h * (d - k))
        (Ideal.Quotient.mk ((maximalIdeal O) ^ (K - h * d)) (a₁ ⟨e' * k, hek⟩))
      = resDig π (h * (d - k))
        (Ideal.Quotient.mk ((maximalIdeal O) ^ K) (a₁ ⟨e' * k, hek⟩))
    rw [resDig_mk hπ (by omega), resDig_mk hπ (by omega)]
  -- the face and stratum data at the shifted window
  obtain ⟨-, hA0', hAm', hvis'⟩ :=
    leafCone_face_data hh hhe hd0 rfl hn0 hnK' hcone' hcorner''
  have hstr' : proj O (e' * d) (K - h * d) a₁
      ∈ levelZeroStratum O (e' * d) (K - h * d) (Polynomial.X ^ (e' * d)) := by
    refine (mem_stratum_X_pow_iff (by omega : 1 ≤ K - h * d) _).2 fun i => ?_
    have h1 := hcone' i
    have h2 : 0 < h * (e' * d - (i : ℕ)) :=
      Nat.mul_pos (by omega) (by have := i.isLt; omega)
    rcases Nat.eq_zero_or_pos (resOrd (proj O (e' * d) (K - h * d) a₁ i)) with h3 | h3
    · rw [h3, Nat.mul_zero] at h1
      omega
    · exact h3
  -- the residual is irreducible at the shifted window (the bridge, both windows)
  have hirrC' : Irreducible (classResidualPoly π (proj O (e' * d) (K - h * d) a₁) h e') := by
    refine (irreducible_classResidualPoly_iff hπ hh hhe hd0 rfl hn0 hnK'
      hcone' hcorner'').mpr ?_
    rw [hdig]
    exact hirr
  exact decidedAt_of_spanning_irr hd0 hπ hn0 hh he'0 hcop rfl hstr' hA0' hAm' hvis' hirrC'

/-- ★★ **THE IMAGE**: the `mulClass` of a pinned-box class and a steep linear class
IS a sub-face leaf cell at the frame `(h, e', d)` — decided (both drainage legs
discharged), stratified, shallow, non-pure-face, with minimal face `(h, e')` not
attained at `0` and irreducible degree-`d` residual. -/
theorem mul_mem_subfaceCell {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d)
    {σ : FactorizationType} (hσ : σ.data = (e', d) ::ₘ {(1, 1)}) {M : ℕ}
    (hM : h * d ≤ M)
    {γ : Coeff O (e' * d) (M + (e' * d + 1))} {ρ : Coeff O 1 (M + (e' * d + 1))}
    (hγ : γ ∈ pinnedBox π (M + (e' * d + 1)) h e' d)
    (hρ : ρ ∈ steepLin O (M + (e' * d + 1))) :
    mulClass γ ρ ∈ subfaceCell O π (e' * d + 1) h e' d σ M := by
  have hh : 0 < h := hh1
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hhd : h * d < e' * d := by
    have := (Nat.mul_lt_mul_right hd0).mpr hhe
    omega
  obtain ⟨a₁, rfl⟩ := proj_surjective O (e' * d) (M + (e' * d + 1)) γ
  obtain ⟨a₂, rfl⟩ := proj_surjective O 1 (M + (e' * d + 1)) ρ
  obtain ⟨hcone, hcorner, hirr⟩ := hγ
  have hsteep : 1 ≤ resOrd (proj O 1 (M + (e' * d + 1)) a₂ 0) := hρ
  -- window arithmetic
  have hhdK : h * d + 1 ≤ M + (e' * d + 1) := by omega
  have hmK : e' * d + 1 ≤ M + (e' * d + 1) := by omega
  -- the three coefficient facts and the face package
  obtain ⟨hconeP, honeP, hzeroP⟩ :=
    prod_class_data hπ hh hhe hd0 hhdK hcone hcorner hsteep
  obtain ⟨hF, hnA0, hstr, hsh, hnpure⟩ :=
    face_package hh1 hhe hcop hd0 hmK hconeP honeP hzeroP
  -- the residual: irreducible of degree d
  obtain ⟨u, huu, hfac, -, hdegP⟩ :=
    prod_residual hπ hh hhe hcop hd0 hmK hhdK hcone hcorner hsteep
  have hcorner' : resOrd (proj O (e' * d) (M + (e' * d + 1)) a₁ ⟨0, hn0⟩) = h * d := by
    rw [← resAt_lt (proj O (e' * d) (M + (e' * d + 1)) a₁) hn0]
    exact hcorner
  have hirrA : Irreducible
      (classResidualPoly π (proj O (e' * d) (M + (e' * d + 1)) a₁) h e') :=
    (irreducible_classResidualPoly_iff hπ hh hhe hd0 rfl hn0 (by omega)
      hcone hcorner').mpr hirr
  have hirrC : Irreducible (classResidualPoly π (proj O (e' * d + 1) (M + (e' * d + 1))
      (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e') := by
    rw [hfac]
    letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
    have hassoc : Associated
        (classResidualPoly π (proj O (e' * d) (M + (e' * d + 1)) a₁) h e')
        (classResidualPoly π (proj O (e' * d) (M + (e' * d + 1)) a₁) h e' * u) :=
      ⟨huu.unit, by rw [IsUnit.unit_spec]⟩
    exact hassoc.irreducible hirrA
  -- the decidedness: DPN's coupling with both shifted legs discharged
  have hK2 : 2 * (h * d) < M + (e' * d + 1) := by omega
  have hKm : e' * d + h * d ≤ M + (e' * d + 1) := by omega
  have hdec₁ := box_decided_shifted hπ hh hhe hcop hd0 hK2 hKm hcone hcorner hirr
  have hdec₂ : DecidedAt O 1 ⟨{(1, 1)}⟩ (M + (e' * d + 1) - h * d)
      (proj O 1 (M + (e' * d + 1) - h * d) a₂) := decidedAt_linear _
  have hsteep' : ∀ j : Fin 1, h * (1 - (j : ℕ))
      < e' * resOrd (proj O 1 (M + (e' * d + 1)) a₂ j) := by
    intro j
    have hj0 : j = 0 := Subsingleton.elim j 0
    subst hj0
    have h1 : e' * 1 ≤ e' * resOrd (proj O 1 (M + (e' * d + 1)) a₂ 0) :=
      Nat.mul_le_mul_left e' hsteep
    have hj : ((0 : Fin 1) : ℕ) = 0 := rfl
    rw [hj]
    omega
  have hlev : M + (e' * d + 1) - h * d = M + (e' * d + 1) - h * d * 1 := by
    rw [Nat.mul_one]
  rw [hlev] at hdec₁ hdec₂
  have hdec := decidedAt_mulClass_of_cones hπ he'0 hd0 one_pos
    (by rw [Nat.mul_one]; omega : 2 * (h * d * 1) + 1 ≤ M + (e' * d + 1))
    hcone hcorner' hsteep' hdec₁ hdec₂
  have hdata : (FactorizationType.mk {(e', d)}).data
      + (FactorizationType.mk {(1, 1)}).data = σ.data := by
    show ({(e', d)} : Multiset (ℕ × ℕ)) + {(1, 1)} = σ.data
    rw [hσ, Multiset.singleton_add]
  rw [hdata] at hdec
  have hσeta : (⟨σ.data⟩ : FactorizationType) = σ := rfl
  rw [hσeta] at hdec
  -- assembly through `mulClass_proj`
  rw [← mulClass_proj a₁ a₂] at hdec ⊢
  exact ⟨⟨⟨⟨⟨hdec, hstr⟩, hsh⟩, hnpure⟩, h, e', hF, hirrC, hnA0⟩, hF, hdegP⟩

end Image

/-! ## §5 — SURJECTIVITY: every sub-face cell at an r = 1 frame factors through the
carriers, and the type is FORCED to `(e', d) ::ₘ {(1, 1)}` -/

section Surjectivity

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **THE FACTORIZATION OF THE CELL** (LSF's transport pushed into the carriers):
every sub-face cell at an r = 1 frame is `mulClass γ ρ` for a pinned-box class `γ`
and a steep linear class `ρ` — and the ambient type is forced. -/
theorem subfaceCell_factors {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O (e' * d + 1) (M + (e' * d + 1))}
    (hc : c ∈ subfaceCell O π (e' * d + 1) h e' d σ M) :
    σ.data = (e', d) ::ₘ {(1, 1)}
      ∧ ∃ (γ : Coeff O (e' * d) (M + (e' * d + 1)))
          (ρ : Coeff O 1 (M + (e' * d + 1))),
          γ ∈ pinnedBox π (M + (e' * d + 1)) h e' d
            ∧ ρ ∈ steepLin O (M + (e' * d + 1)) ∧ mulClass γ ρ = c := by
  have hh : 0 < h := hh1
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hm0 : 0 < e' * d + 1 := by omega
  have hhd : h * d < e' * d := by
    have := (Nat.mul_lt_mul_right hd0).mpr hhe
    omega
  obtain ⟨hsub, hF, hdeg⟩ := hc
  obtain ⟨a, ha⟩ := proj_surjective O (e' * d + 1) (M + (e' * d + 1)) c
  obtain ⟨g, R, d', heq, hgm, hRm, hgpure, hd'0, hgd, hd'm, htyg, hRdeg, hdata,
    hcrpd, hside⟩ := subface_transport_pinned hπ hm0 hsub hF ha
  -- the transported degree is the frame degree
  have hd' : d' = d := by
    rw [hcrpd] at hdeg
    exact hdeg
  rw [hd'] at hd'0 hgd hd'm htyg hRdeg hdata
  have hR1 : R.natDegree = 1 := by omega
  -- the two carrier classes
  have hmpg : monicPoly (fun i : Fin (e' * d) => g.coeff (i : ℕ)) = g :=
    monicPoly_coeff_eq_self hgm hgd
  have hmpR : monicPoly (fun i : Fin 1 => R.coeff (i : ℕ)) = R :=
    monicPoly_coeff_eq_self hRm hR1
  -- the steep read on ρ
  have hsteep : 1 ≤ resOrd (proj O 1 (M + (e' * d + 1))
      (fun i : Fin 1 => R.coeff (i : ℕ)) 0) := by
    have hsc := strict_cone_of_side_singleton hRm hside (show 0 < R.natDegree by omega)
    have h0 : (0 : ℕ∞) < e' • npHgt X R 0 := lt_of_le_of_lt (zero_le) hsc
    have hne : npHgt X R 0 ≠ 0 := by
      intro h00
      rw [h00, smul_zero] at h0
      exact lt_irrefl 0 h0
    rw [npHgt_X] at hne
    have h1 : (1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal O (R.coeff 0) :=
      Order.one_le_iff_ne_zero.mpr hne
    have hdvd : π ^ 1 ∣ R.coeff 0 := by
      refine (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 ?_
      exact_mod_cast h1
    exact (le_classCoeffVal_iff_dvd hπ (by omega : 1 ≤ M + (e' * d + 1)) rfl 0).mpr hdvd
  -- the cone and exact corner on γ (from purity)
  obtain ⟨hpure, hcornerP⟩ := cone_data_of_isPure hπ hgm he'0 hd0 hgpure hgd
    (show h * d < M + (e' * d + 1) by omega)
  have hcornerAt : resOrd (resAt (proj O (e' * d) (M + (e' * d + 1))
      (fun i => g.coeff (i : ℕ))) 0) = h * d := by
    rw [resAt_lt _ hn0]
    exact hcornerP
  -- the product class IS c
  have hprodeq : monicPoly (fun i : Fin (e' * d) => g.coeff (i : ℕ))
      * monicPoly (fun i : Fin 1 => R.coeff (i : ℕ)) = monicPoly a := by
    rw [hmpg, hmpR, ← heq]
  have hveceq : (fun i : Fin (e' * d + 1) =>
      (monicPoly (fun i : Fin (e' * d) => g.coeff (i : ℕ))
        * monicPoly (fun i : Fin 1 => R.coeff (i : ℕ))).coeff (i : ℕ)) = a := by
    funext i
    rw [hprodeq]
    exact monicPoly_coeff_lt a i.isLt
  have hmul : mulClass (proj O (e' * d) (M + (e' * d + 1)) (fun i => g.coeff (i : ℕ)))
      (proj O 1 (M + (e' * d + 1)) (fun i => R.coeff (i : ℕ))) = c := by
    rw [← mulClass_proj, hveceq, ha]
  -- the residual factorization pulls the cell's irreducibility back to γ
  obtain ⟨u, huu, hfac, -, -⟩ := prod_residual hπ hh hhe hcop hd0
    (by omega) (by omega) hpure hcornerAt hsteep
  rw [hveceq, ha] at hfac
  have hirrc : Irreducible (classResidualPoly π c h e') := by
    obtain ⟨-, h₃, e₃, hF₃, hirr₃, -⟩ := hsub
    obtain ⟨hh3, he3⟩ := minFaceAt_unique hF hF₃
    rw [← hh3, ← he3] at hirr₃
    exact hirr₃
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hirrγ : Irreducible (classResidualPoly π
      (proj O (e' * d) (M + (e' * d + 1)) (fun i => g.coeff (i : ℕ))) h e') := by
    have hassoc : Associated
        (classResidualPoly π (proj O (e' * d) (M + (e' * d + 1))
          (fun i => g.coeff (i : ℕ))) h e')
        (classResidualPoly π c h e') := by
      rw [hfac]
      exact ⟨huu.unit, by rw [IsUnit.unit_spec]⟩
    exact hassoc.symm.irreducible hirrc
  have hirrleaf : Irreducible (leafResPoly π h e' d
      (proj O (e' * d) (M + (e' * d + 1)) (fun i => g.coeff (i : ℕ)))) :=
    (irreducible_classResidualPoly_iff hπ hh hhe hd0 rfl hn0 (by omega)
      hpure hcornerP).mp hirrγ
  -- the type forcing
  have htyR : typeOf R = ⟨{(1, 1)}⟩ := typeOf_of_natDegree_one hRm hR1
  have hσ : σ.data = (e', d) ::ₘ {(1, 1)} := by
    rw [hdata, htyR]
  exact ⟨hσ, proj O (e' * d) (M + (e' * d + 1)) (fun i => g.coeff (i : ℕ)),
    proj O 1 (M + (e' * d + 1)) (fun i => R.coeff (i : ℕ)),
    ⟨hpure, hcornerAt, hirrleaf⟩, hsteep, hmul⟩

/-- ★ **Off-type emptiness at r = 1**: if `σ.data ≠ (e', d) ::ₘ {(1, 1)}`, the
r = 1 sub-face cell is EMPTY at every level. -/
theorem subfaceCell_r_one_empty {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d)
    {σ : FactorizationType} (hσ : σ.data ≠ (e', d) ::ₘ {(1, 1)}) (M : ℕ) :
    subfaceCell O π (e' * d + 1) h e' d σ M
      = (∅ : Set (Coeff O (e' * d + 1) (M + (e' * d + 1)))) := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hc
  exact hσ (subfaceCell_factors hπ hh1 hhe hcop hd0 hc).1

end Surjectivity

/-! ## §6 — THE SEPARATION: the `mulClass` fiber over a cell is EXACTLY one
`pairNbhd` cluster (Hensel-free at r = 1 — evaluate at the steep root) -/

section Separation

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The corner threshold is beaten strictly at every positive abscissa once the
steep root contributes its valuation: `h·d + 1 ≤ tLeaf (e'd) j + j` for `j ≥ 1`. -/
private theorem corner_lt_tLeaf_add {h e' d : ℕ} (hh : 0 < h) (hhe : h < e')
    (hd0 : 0 < d) {j : ℕ} (hj1 : 1 ≤ j) :
    h * d + 1 ≤ tLeaf h e' (e' * d) j + j := by
  have he'0 : 0 < e' := by omega
  have hhd : h * d < e' * d := by
    have := (Nat.mul_lt_mul_right hd0).mpr hhe
    omega
  by_cases hjn : e' * d ≤ j
  · omega
  · have hB : h * (e' * d - j) ≤ e' * tLeaf h e' (e' * d) j :=
      (tLeaf_le_iff he'0 h (e' * d) j _).mp le_rfl
    have hsplit : h * (e' * d - j) + h * j = h * (e' * d) := by
      have h4 : e' * d - j + j = e' * d := by omega
      calc h * (e' * d - j) + h * j = h * ((e' * d - j) + j) := by ring
        _ = h * (e' * d) := by rw [h4]
    have hE : h * (e' * d) = e' * (h * d) := by ring
    have hjb : h * j + j ≤ e' * j := by
      have h5 : (h + 1) * j ≤ e' * j := Nat.mul_le_mul_right j (by omega)
      have h6 : (h + 1) * j = h * j + j := by ring
      omega
    have hF : e' * (tLeaf h e' (e' * d) j + j) = e' * tLeaf h e' (e' * d) j + e' * j := by
      ring
    have hlt : e' * (h * d) < e' * (tLeaf h e' (e' * d) j + j) := by omega
    have := Nat.lt_of_mul_lt_mul_left hlt
    omega

/-- The pinned-box lift divisibility bank: the threshold divisibilities and the
exact corner pair, on any lift of a pinned-box-data class. -/
private theorem box_lift_divs {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) {K : ℕ} (hhdK : h * d < K)
    {a₁ : Fin (e' * d) → O}
    (hcone : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) K a₁ j))
    (hcorner : resOrd (resAt (proj O (e' * d) K a₁) 0) = h * d) :
    (∀ j : Fin (e' * d), π ^ (tLeaf h e' (e' * d) (j : ℕ)) ∣ a₁ j)
      ∧ ∀ j : Fin (e' * d), (j : ℕ) = 0 →
          π ^ (h * d) ∣ a₁ j ∧ ¬ π ^ (h * d + 1) ∣ a₁ j := by
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hcorner' : resOrd (proj O (e' * d) K a₁ ⟨0, hn0⟩) = h * d := by
    rw [← resAt_lt (proj O (e' * d) K a₁) hn0]
    exact hcorner
  have hvis0 : classCoeffVal (proj O (e' * d) K a₁) ⟨0, hn0⟩ < K := by
    show resOrd (proj O (e' * d) K a₁ ⟨0, hn0⟩) < K
    omega
  have hL1 := classCoeffVal_exact hπ rfl hvis0
  rw [show classCoeffVal (proj O (e' * d) K a₁) ⟨0, hn0⟩ = h * d from hcorner'] at hL1
  refine ⟨fun j => ?_, fun j hj0 => ?_⟩
  · have h1 : tLeaf h e' (e' * d) (j : ℕ) ≤ resOrd (proj O (e' * d) K a₁ j) :=
      (tLeaf_le_iff he'0 h (e' * d) (j : ℕ) _).mpr (hcone j)
    have h2 : π ^ (resOrd (proj O (e' * d) K a₁ j)) ∣ a₁ j :=
      (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
    exact (pow_dvd_pow π h1).trans h2
  · have hj : j = ⟨0, hn0⟩ := by
      ext
      exact hj0
    rw [hj]
    exact hL1

/-- ★★ **THE FIBER IS ONE CLUSTER**: over the product class of a carrier pair, the
`mulClass` fiber inside (pinned box) × (steep linear) is EXACTLY the depth-`h·d`
pair neighborhood.  Separation (⊆): evaluate the level-`K` product congruence at
the steep root `−α`; the box pins `π^(h·d) ∥ g(−α)` exactly, forcing the roots
together mod `π^(K−h·d)`; the monic cancellation recovers the block side.
Stability (⊇): every box/steep read lives at digit levels `≤ h·d < h·d + 1`. -/
private theorem fiber_eq_pairNbhd {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) {K : ℕ} (hK2 : 2 * (h * d) + 1 ≤ K)
    {a₁ : Fin (e' * d) → O} {a₂ : Fin 1 → O}
    (hcone : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) K a₁ j))
    (hcorner : resOrd (resAt (proj O (e' * d) K a₁) 0) = h * d)
    (hirr : Irreducible (leafResPoly π h e' d (proj O (e' * d) K a₁)))
    (hsteep : 1 ≤ resOrd (proj O 1 K a₂ 0)) :
    (pinnedBox π K h e' d ×ˢ steepLin O K)
        ∩ (fun p : Coeff O (e' * d) K × Coeff O 1 K => mulClass p.1 p.2) ⁻¹'
            {mulClass (proj O (e' * d) K a₁) (proj O 1 K a₂)}
      = pairNbhd π K (h * d) a₁ a₂ := by
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hhd : h * d < e' * d := by
    have := (Nat.mul_lt_mul_right hd0).mpr hhe
    omega
  have hhdK : h * d < K := by omega
  obtain ⟨hL2a, hL1a⟩ := box_lift_divs hπ hh hhe hd0 hhdK hcone hcorner
  have hαa : π ∣ a₂ 0 := by
    have h2 : π ^ 1 ∣ a₂ 0 :=
      (le_classCoeffVal_iff_dvd hπ (by omega : 1 ≤ K) rfl 0).mp hsteep
    rwa [pow_one] at h2
  ext ⟨c₁, c₂⟩
  simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · -- SEPARATION
    rintro ⟨⟨hc₁, hc₂⟩, hpre⟩
    obtain ⟨w₁, rfl⟩ := proj_surjective O (e' * d) K c₁
    obtain ⟨w₂, rfl⟩ := proj_surjective O 1 K c₂
    obtain ⟨hconeW, hcornerW, -⟩ := hc₁
    obtain ⟨hL2w, hL1w⟩ := box_lift_divs hπ hh hhe hd0 hhdK hconeW hcornerW
    have hβw : π ∣ w₂ 0 := by
      have h2 : π ^ 1 ∣ w₂ 0 :=
        (le_classCoeffVal_iff_dvd hπ (by omega : 1 ≤ K) rfl 0).mp hc₂
      rwa [pow_one] at h2
    -- the level-K product congruence
    have hprod : Polynomial.C (π ^ K)
        ∣ monicPoly w₁ * monicPoly w₂ - monicPoly a₁ * monicPoly a₂ :=
      C_pow_dvd_mul_sub_of_mulClass_eq hπ hpre.symm
    -- evaluate at the steep root
    have hEa : (monicPoly a₁ * monicPoly a₂).eval (-(a₂ 0)) = 0 := by
      rw [Polynomial.eval_mul, monicPoly_one_eq a₂]
      simp
    have hEw : (monicPoly w₁ * monicPoly w₂).eval (-(a₂ 0))
        = (monicPoly w₁).eval (-(a₂ 0)) * (-(a₂ 0) + w₂ 0) := by
      rw [Polynomial.eval_mul, monicPoly_one_eq w₂]
      simp
    have hEsub : π ^ K
        ∣ (monicPoly w₁).eval (-(a₂ 0)) * (-(a₂ 0) + w₂ 0) := by
      have h1 := dvd_eval_of_C_dvd hprod (-(a₂ 0))
      rwa [Polynomial.eval_sub, hEa, sub_zero, hEw] at h1
    -- the exact valuation of the block at the steep root
    have hxdvd : π ∣ -(a₂ 0) := (dvd_neg).mpr hαa
    have heval : (monicPoly w₁).eval (-(a₂ 0))
        = (-(a₂ 0)) ^ (e' * d) + ∑ j : Fin (e' * d), w₁ j * (-(a₂ 0)) ^ (j : ℕ) := by
      unfold monicPoly
      rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_finsetSum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X]
    have hEsplit : (monicPoly w₁).eval (-(a₂ 0))
        = w₁ ⟨0, hn0⟩
          + ((-(a₂ 0)) ^ (e' * d)
            + ∑ j ∈ Finset.univ.erase (⟨0, hn0⟩ : Fin (e' * d)),
                w₁ j * (-(a₂ 0)) ^ (j : ℕ)) := by
      rw [heval, ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (⟨0, hn0⟩ : Fin (e' * d)))]
      have h1 : w₁ ⟨0, hn0⟩ * (-(a₂ 0)) ^ (((⟨0, hn0⟩ : Fin (e' * d)) : ℕ)) = w₁ ⟨0, hn0⟩ := by
        show w₁ ⟨0, hn0⟩ * (-(a₂ 0)) ^ (0 : ℕ) = w₁ ⟨0, hn0⟩
        rw [pow_zero, mul_one]
      rw [h1]
      ring
    have hrest : π ^ (h * d + 1)
        ∣ ((-(a₂ 0)) ^ (e' * d)
          + ∑ j ∈ Finset.univ.erase (⟨0, hn0⟩ : Fin (e' * d)),
              w₁ j * (-(a₂ 0)) ^ (j : ℕ)) := by
      refine dvd_add ?_ (Finset.dvd_sum fun j hj => ?_)
      · have h1 : π ^ (e' * d) ∣ (-(a₂ 0)) ^ (e' * d) := pow_dvd_pow_of_dvd hxdvd _
        exact (pow_dvd_pow π (by omega : h * d + 1 ≤ e' * d)).trans h1
      · have hj1 : 1 ≤ (j : ℕ) := by
          rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h1
          · exfalso
            have : j = (⟨0, hn0⟩ : Fin (e' * d)) := by
              ext
              exact h0
            rw [this] at hj
            exact (Finset.notMem_erase _ _) hj
          · exact h1
        have h1 : π ^ (tLeaf h e' (e' * d) (j : ℕ) + (j : ℕ))
            ∣ w₁ j * (-(a₂ 0)) ^ (j : ℕ) := by
          rw [pow_add]
          exact mul_dvd_mul (hL2w j) (pow_dvd_pow_of_dvd hxdvd _)
        exact (pow_dvd_pow π (corner_lt_tLeaf_add hh hhe hd0 hj1)).trans h1
    obtain ⟨hw0dvd, hw0ndvd⟩ := hL1w ⟨0, hn0⟩ rfl
    have hudvd : π ^ (h * d) ∣ (monicPoly w₁).eval (-(a₂ 0)) := by
      rw [hEsplit]
      exact dvd_add hw0dvd ((pow_dvd_pow π (by omega)).trans hrest)
    have hundvd : ¬ π ^ (h * d + 1) ∣ (monicPoly w₁).eval (-(a₂ 0)) := by
      intro hcon
      rw [hEsplit] at hcon
      refine hw0ndvd ?_
      have h2 := dvd_sub hcon hrest
      rwa [add_sub_cancel_right] at h2
    -- cancel the exact block valuation
    obtain ⟨v, hv⟩ := hudvd
    have hvndvd : ¬ π ∣ v := by
      intro hcon
      obtain ⟨z, hz⟩ := hcon
      refine hundvd ?_
      rw [hv, hz, pow_succ]
      exact ⟨z, by ring⟩
    have hvu : IsUnit v := by
      by_contra hcon
      have h1 : v ∈ maximalIdeal O :=
        (IsLocalRing.mem_maximalIdeal v).mpr (mem_nonunits_iff.mpr hcon)
      exact hvndvd ((mem_maximalIdeal_iff_dvd hπ v).1 h1)
    have hcancel : π ^ (K - h * d) ∣ (-(a₂ 0) + w₂ 0) := by
      have h1 : π ^ (h * d) * π ^ (K - h * d) ∣ π ^ (h * d) * (v * (-(a₂ 0) + w₂ 0)) := by
        have h2 : π ^ (h * d) * π ^ (K - h * d) = π ^ K := by
          rw [← pow_add]
          congr 1
          omega
        rw [h2]
        have h3 : π ^ (h * d) * (v * (-(a₂ 0) + w₂ 0))
            = (monicPoly w₁).eval (-(a₂ 0)) * (-(a₂ 0) + w₂ 0) := by
          rw [hv]
          ring
        rw [h3]
        exact hEsub
      have h4 : π ^ (K - h * d) ∣ v * (-(a₂ 0) + w₂ 0) :=
        (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).mp h1
      exact (hvu.dvd_mul_left).mp h4
    have hβα : π ^ (h * d + 1) ∣ w₂ 0 - a₂ 0 := by
      have h1 : π ^ (h * d + 1) ∣ (-(a₂ 0) + w₂ 0) :=
        (pow_dvd_pow π (by omega : h * d + 1 ≤ K - h * d)).trans hcancel
      rwa [neg_add_eq_sub] at h1
    -- the block side: monic cancellation
    have hw₂sub : monicPoly w₂ - monicPoly a₂ = Polynomial.C (w₂ 0 - a₂ 0) := by
      rw [monicPoly_one_eq w₂, monicPoly_one_eq a₂, Polynomial.C_sub]
      ring
    have hCdvd : Polynomial.C (π ^ (K - h * d))
        ∣ (monicPoly w₁ - monicPoly a₁) * monicPoly w₂ := by
      have hidentity : (monicPoly w₁ - monicPoly a₁) * monicPoly w₂
          = (monicPoly w₁ * monicPoly w₂ - monicPoly a₁ * monicPoly a₂)
            - monicPoly a₁ * (monicPoly w₂ - monicPoly a₂) := by
        ring
      rw [hidentity]
      refine dvd_sub ((map_dvd Polynomial.C (pow_dvd_pow π (by omega))).trans hprod) ?_
      rw [hw₂sub]
      have h1 : Polynomial.C (π ^ (K - h * d)) ∣ Polynomial.C (w₂ 0 - a₂ 0) := by
        refine map_dvd Polynomial.C ?_
        have h2 : π ^ (K - h * d) ∣ (-(a₂ 0) + w₂ 0) := hcancel
        rwa [neg_add_eq_sub] at h2
      exact h1.trans (Dvd.intro_left _ rfl)
    have hCdvd₁ : Polynomial.C (π ^ (K - h * d)) ∣ monicPoly w₁ - monicPoly a₁ :=
      C_dvd_of_C_dvd_mul_monic (monicPoly_monic w₂) hCdvd
    refine ⟨hpre, ⟨w₁, rfl, fun i => ?_⟩, ⟨w₂, rfl, fun i => ?_⟩⟩
    · have h1 := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hCdvd₁ (i : ℕ)
      rw [Polynomial.coeff_sub, monicPoly_coeff_lt w₁ i.isLt,
        monicPoly_coeff_lt a₁ i.isLt] at h1
      exact (pow_dvd_pow π (by omega : h * d + 1 ≤ K - h * d)).trans h1
    · have hi0 : i = 0 := Subsingleton.elim i 0
      rw [hi0]
      exact hβα
  · -- STABILITY
    rintro ⟨hpre, ⟨b₁, rfl, hcong₁⟩, ⟨b₂, rfl, hcong₂⟩⟩
    refine ⟨⟨?_, ?_⟩, hpre⟩
    · -- the perturbed block class stays in the pinned box
      have hb₁divs : ∀ j : Fin (e' * d), π ^ (tLeaf h e' (e' * d) (j : ℕ)) ∣ b₁ j := by
        intro j
        have h1 : b₁ j = a₁ j + (b₁ j - a₁ j) := by ring
        rw [h1]
        refine dvd_add (hL2a j) ?_
        have h2 : tLeaf h e' (e' * d) (j : ℕ) ≤ h * d + 1 := by
          have := tLeaf_le_corner he'0 h d (j : ℕ)
          omega
        exact (pow_dvd_pow π h2).trans (hcong₁ j)
      have hconeB : ∀ j : Fin (e' * d),
          h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) K b₁ j) := by
        intro j
        have h1 : tLeaf h e' (e' * d) (j : ℕ) ≤ resOrd (proj O (e' * d) K b₁ j) := by
          refine (le_classCoeffVal_iff_dvd hπ ?_ rfl j).mpr (hb₁divs j)
          have := tLeaf_le_corner he'0 h d (j : ℕ)
          omega
        have h2 : h * (e' * d - (j : ℕ)) ≤ e' * tLeaf h e' (e' * d) (j : ℕ) :=
          (tLeaf_le_iff he'0 h (e' * d) (j : ℕ) _).mp le_rfl
        have h3 : e' * tLeaf h e' (e' * d) (j : ℕ)
            ≤ e' * resOrd (proj O (e' * d) K b₁ j) := Nat.mul_le_mul_left e' h1
        omega
      obtain ⟨ha0dvd, ha0ndvd⟩ := hL1a ⟨0, hn0⟩ rfl
      have hb0dvd : π ^ (h * d) ∣ b₁ ⟨0, hn0⟩ := by
        have h1 : b₁ ⟨0, hn0⟩ = a₁ ⟨0, hn0⟩ + (b₁ ⟨0, hn0⟩ - a₁ ⟨0, hn0⟩) := by ring
        rw [h1]
        exact dvd_add ha0dvd ((pow_dvd_pow π (by omega)).trans (hcong₁ ⟨0, hn0⟩))
      have hb0ndvd : ¬ π ^ (h * d + 1) ∣ b₁ ⟨0, hn0⟩ := by
        intro hcon
        refine ha0ndvd ?_
        have h1 : a₁ ⟨0, hn0⟩ = b₁ ⟨0, hn0⟩ - (b₁ ⟨0, hn0⟩ - a₁ ⟨0, hn0⟩) := by ring
        rw [h1]
        exact dvd_sub hcon (hcong₁ ⟨0, hn0⟩)
      have hcornerB : resOrd (resAt (proj O (e' * d) K b₁) 0) = h * d := by
        rw [resAt_lt _ hn0]
        show resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ K) (b₁ ⟨0, hn0⟩)) = h * d
        exact resOrd_mk_eq hπ (by omega) hb0dvd (Or.inr hb0ndvd)
      have hdigB : leafResPoly π h e' d (proj O (e' * d) K b₁)
          = leafResPoly π h e' d (proj O (e' * d) K a₁) := by
        refine (leafResPoly_eq_iff π h e' d _ (leafResPoly_monic π h e' d _)
          (leafResPoly_natDegree π h e' d _)).mpr fun k hk => ?_
        have hek : e' * k < e' * d := by
          have h1 : e' * (k + 1) ≤ e' * d := Nat.mul_le_mul_left e' (by omega)
          have h2 : e' * (k + 1) = e' * k + e' := by ring
          omega
        rw [leafResPoly_coeff_lt π h e' d _ hk]
        unfold leafDig
        rw [resAt_lt _ hek, resAt_lt _ hek]
        show resDig π (h * (d - k))
            (Ideal.Quotient.mk ((maximalIdeal O) ^ K) (b₁ ⟨e' * k, hek⟩))
          = resDig π (h * (d - k))
            (Ideal.Quotient.mk ((maximalIdeal O) ^ K) (a₁ ⟨e' * k, hek⟩))
        have hlev : h * (d - k) < K := by
          have h1 : h * (d - k) ≤ h * d := Nat.mul_le_mul_left h (Nat.sub_le _ _)
          omega
        rw [resDig_mk hπ hlev, resDig_mk hπ hlev]
        refine digAt_congr hπ ?_ (hcong₁ ⟨e' * k, hek⟩)
        have h1 : h * (d - k) ≤ h * d := Nat.mul_le_mul_left h (Nat.sub_le _ _)
        omega
      exact ⟨hconeB, hcornerB, by rw [hdigB]; exact hirr⟩
    · -- the perturbed steep class stays steep
      have h1 : π ∣ b₂ 0 := by
        have h2 : b₂ 0 = a₂ 0 + (b₂ 0 - a₂ 0) := by ring
        rw [h2]
        refine dvd_add hαa ?_
        have h3 : π ^ 1 ∣ b₂ 0 - a₂ 0 :=
          (pow_dvd_pow π (by omega : 1 ≤ h * d + 1)).trans (hcong₂ 0)
        rwa [pow_one] at h3
      show 1 ≤ resOrd (proj O 1 K b₂ 0)
      refine (le_classCoeffVal_iff_dvd hπ (by omega : 1 ≤ K) rfl 0).mpr ?_
      rwa [pow_one]

end Separation

/-! ## §7 — ★★★ THE COUNT AND THE LAW: `#subfaceCell · q^(h·d) = #pinnedBox · #steepLin`
exactly, hence `SubfaceFrameLaw` at every r = 1 frame, UNCONDITIONAL -/

section Law

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **THE COUNT IDENTITY** (exact at every level `M ≥ h·d`): the r = 1 sub-face
cell count times the cluster size is the carrier product count — the bijection up
to `q^(h·d)`-clusters, assembled from the image, the factorization, and the
fiber law. -/
private theorem card_cell_mul {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d)
    {σ : FactorizationType} (hσ : σ.data = (e', d) ::ₘ {(1, 1)}) {M : ℕ}
    (hM : h * d ≤ M) :
    Nat.card (subfaceCell O π (e' * d + 1) h e' d σ M)
        * residueCard O ^ (h * d)
      = Nat.card (pinnedBox π (M + (e' * d + 1)) h e' d
          : Set (Coeff O (e' * d) (M + (e' * d + 1))))
        * Nat.card (steepLin O (M + (e' * d + 1))) := by
  classical
  have hh : 0 < h := hh1
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hhd : h * d < e' * d := by
    have := (Nat.mul_lt_mul_right hd0).mpr hhe
    omega
  have hK2 : 2 * (h * d) + 1 ≤ M + (e' * d + 1) := by omega
  letI : Fintype (Coeff O (e' * d) (M + (e' * d + 1)) × Coeff O 1 (M + (e' * d + 1))) :=
    Fintype.ofFinite _
  have hTfin : (subfaceCell O π (e' * d + 1) h e' d σ M).Finite := Set.toFinite _
  -- the fiber decomposition over the cell
  have hsum : Nat.card ((pinnedBox π (M + (e' * d + 1)) h e' d
        ×ˢ steepLin O (M + (e' * d + 1)))
        : Set (Coeff O (e' * d) (M + (e' * d + 1)) × Coeff O 1 (M + (e' * d + 1))))
      = ∑ c ∈ hTfin.toFinset,
          Nat.card (((pinnedBox π (M + (e' * d + 1)) h e' d
              ×ˢ steepLin O (M + (e' * d + 1)))
            ∩ (fun p : Coeff O (e' * d) (M + (e' * d + 1))
                × Coeff O 1 (M + (e' * d + 1)) => mulClass p.1 p.2) ⁻¹' {c})
            : Set (Coeff O (e' * d) (M + (e' * d + 1))
                × Coeff O 1 (M + (e' * d + 1)))) := by
    refine natCard_eq_sum_fiber _ _ _ fun p hp => ?_
    rw [Set.Finite.mem_toFinset]
    exact mul_mem_subfaceCell hπ hh1 hhe hcop hd0 hσ hM hp.1 hp.2
  -- every fiber is one cluster of size exactly `q^(h·d)`
  have hfib : ∀ c ∈ hTfin.toFinset,
      Nat.card (((pinnedBox π (M + (e' * d + 1)) h e' d
          ×ˢ steepLin O (M + (e' * d + 1)))
        ∩ (fun p : Coeff O (e' * d) (M + (e' * d + 1))
            × Coeff O 1 (M + (e' * d + 1)) => mulClass p.1 p.2) ⁻¹' {c})
        : Set (Coeff O (e' * d) (M + (e' * d + 1))
            × Coeff O 1 (M + (e' * d + 1))))
      = residueCard O ^ (h * d) := by
    intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    obtain ⟨-, γ, ρ, hγ, hρ, hmul⟩ :=
      subfaceCell_factors hπ hh1 hhe hcop hd0 hc
    obtain ⟨a₁, rfl⟩ := proj_surjective O (e' * d) (M + (e' * d + 1)) γ
    obtain ⟨a₂, rfl⟩ := proj_surjective O 1 (M + (e' * d + 1)) ρ
    obtain ⟨hcone, hcorner, hirr⟩ := hγ
    rw [← hmul, fiber_eq_pairNbhd hπ hh hhe hd0 hK2 hcone hcorner hirr hρ]
    have hcorner' : resOrd (proj O (e' * d) (M + (e' * d + 1)) a₁
        ⟨0, Nat.mul_pos he'0 hd0⟩) = h * d := by
      rw [← resAt_lt (proj O (e' * d) (M + (e' * d + 1)) a₁) hn0]
      exact hcorner
    have hsteep' : ∀ j : Fin 1, h * (1 - (j : ℕ))
        < e' * resOrd (proj O 1 (M + (e' * d + 1)) a₂ j) := by
      intro j
      have hj0 : j = 0 := Subsingleton.elim j 0
      subst hj0
      have h1 : e' * 1 ≤ e' * resOrd (proj O 1 (M + (e' * d + 1)) a₂ 0) :=
        Nat.mul_le_mul_left e' hρ
      have hj : ((0 : Fin 1) : ℕ) = 0 := rfl
      rw [hj]
      omega
    have hcnt := natCard_pairNbhd_of_cones hπ he'0 hd0 one_pos
      (by rw [Nat.mul_one]; omega : 2 * (h * d * 1) + 1 ≤ M + (e' * d + 1))
      hcone hcorner' hsteep'
    rwa [show h * d * 1 = h * d from Nat.mul_one _] at hcnt
  -- assemble
  have hprod : Nat.card ((pinnedBox π (M + (e' * d + 1)) h e' d
        ×ˢ steepLin O (M + (e' * d + 1)))
        : Set (Coeff O (e' * d) (M + (e' * d + 1)) × Coeff O 1 (M + (e' * d + 1))))
      = Nat.card (pinnedBox π (M + (e' * d + 1)) h e' d
          : Set (Coeff O (e' * d) (M + (e' * d + 1))))
        * Nat.card (steepLin O (M + (e' * d + 1))) := by
    rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
  have hTcard : hTfin.toFinset.card
      = Nat.card (subfaceCell O π (e' * d + 1) h e' d σ M) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hTfin]
  rw [← hprod, hsum, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, hTcard]

/-- ★★★ **THE PER-FRAME LAW AT r = 1, UNCONDITIONAL**: `SubfaceFrameLaw m h e' d σ`
at every frame with `m = e'·d + 1` — the count is eventually the CONSTANT
`nz_d(q)/q^(wLeaf + h·d + 1)` when `σ` matches the forced type, and the cell is
empty otherwise.  No value laws, no drainage premises: the r = 1 steep census and
both decidedness legs are exact. -/
theorem subfaceFrameLaw_r_one (m h e' d : ℕ) (σ : FactorizationType)
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 1 ≤ d)
    (hm : m = e' * d + 1) : SubfaceFrameLaw m h e' d σ := by
  subst hm
  have hh : 0 < h := hh1
  have he'0 : 0 < e' := by omega
  have hd0' : 0 < d := hd0
  have hhd : h * d < e' * d := by
    have := (Nat.mul_lt_mul_right hd0').mpr hhe
    omega
  by_cases hσc : σ.data = (e', d) ::ₘ {(1, 1)}
  · -- the matched type: the eventually-constant law
    refine ⟨nzPoly d, Polynomial.X ^ (wLeaf h e' d + h * d + 1),
      pow_ne_zero _ Polynomial.X_ne_zero, ?_⟩
    intro O _ _ _ _ _
    letI : Fintype (IsLocalRing.ResidueField O) := Fintype.ofFinite _
    have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
    have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hden : (Polynomial.X ^ (wLeaf h e' d + h * d + 1) : Polynomial ℚ).eval
        ((residueCard O : ℕ) : ℚ) ≠ 0 := by
      rw [Polynomial.eval_pow, Polynomial.eval_X]
      exact pow_ne_zero _ hqQ
    refine ⟨hden, ?_⟩
    intro π hπ
    have hqcard : residueCard O = Fintype.card (IsLocalRing.ResidueField O) :=
      Nat.card_eq_fintype_card
    -- the limit value
    have hval : ((((nzPoly d).eval ((residueCard O : ℕ) : ℚ))
          / ((Polynomial.X ^ (wLeaf h e' d + h * d + 1) : Polynomial ℚ).eval
              ((residueCard O : ℕ) : ℚ)) : ℚ) : ℝ)
        = ((Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ))
            / ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d + 1) := by
      have hnum : (nzPoly d).eval ((residueCard O : ℕ) : ℚ)
          = (Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℚ) := by
        rw [hqcard]
        exact nzPoly_eval_card (IsLocalRing.ResidueField O) hd0
      rw [hnum, Polynomial.eval_pow, Polynomial.eval_X]
      push_cast
      ring
    rw [hval]
    -- eventual constancy at `M ≥ h·d`
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    refine Filter.eventuallyEq_of_mem (Filter.Ici_mem_atTop (h * d)) fun M hM => ?_
    have hM' : h * d ≤ M := hM
    have hKn : e' * d ≤ M + (e' * d + 1) := by omega
    have hKhd : h * d < M + (e' * d + 1) := by omega
    have hK1 : 1 ≤ M + (e' * d + 1) := by omega
    -- the exact ℕ identity
    have hcell := card_cell_mul hπ hh1 hhe hcop hd0' hσc hM'
    rw [card_pinnedBox hπ hh hhe hd0' hKn hKhd, card_steepLin hπ hK1] at hcell
    have hw : wLeaf h e' d ≤ (e' * d) * (M + (e' * d + 1)) := by
      have h1 := wLeaf_le_sq (h := h) (e' := e') (d := d) hh hhe hd0'
      have h2 : (e' * d) * (e' * d) ≤ (e' * d) * (M + (e' * d + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hNat : Nat.card (subfaceCell O π (e' * d + 1) h e' d σ M)
          * residueCard O ^ (h * d + (wLeaf h e' d + 1))
        = Nat.card (nzGenre (IsLocalRing.ResidueField O) d)
          * residueCard O ^ ((e' * d + 1) * (M + (e' * d + 1))) := by
      have h1 : residueCard O ^ (h * d + (wLeaf h e' d + 1))
          = residueCard O ^ (h * d) * residueCard O ^ (wLeaf h e' d + 1) := by
        rw [← pow_add]
      have h2 : ((e' * d) * (M + (e' * d + 1)) - wLeaf h e' d)
            + (M + (e' * d + 1) - 1) + (wLeaf h e' d + 1)
          = (e' * d + 1) * (M + (e' * d + 1)) := by
        have h3 : (e' * d + 1) * (M + (e' * d + 1))
            = (e' * d) * (M + (e' * d + 1)) + (M + (e' * d + 1)) := by ring
        omega
      calc Nat.card (subfaceCell O π (e' * d + 1) h e' d σ M)
            * residueCard O ^ (h * d + (wLeaf h e' d + 1))
          = Nat.card (subfaceCell O π (e' * d + 1) h e' d σ M)
              * residueCard O ^ (h * d) * residueCard O ^ (wLeaf h e' d + 1) := by
            rw [h1]; ring
        _ = Nat.card (nzGenre (IsLocalRing.ResidueField O) d)
              * residueCard O ^ ((e' * d) * (M + (e' * d + 1)) - wLeaf h e' d)
              * residueCard O ^ (M + (e' * d + 1) - 1)
              * residueCard O ^ (wLeaf h e' d + 1) := by
            rw [hcell]
        _ = Nat.card (nzGenre (IsLocalRing.ResidueField O) d)
              * residueCard O ^ ((e' * d + 1) * (M + (e' * d + 1))) := by
            rw [← h2, pow_add, pow_add]; ring
    -- the ℝ identity
    symm
    show (Nat.card (subfaceCell O π (e' * d + 1) h e' d σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((e' * d + 1) * (M + (e' * d + 1)))
      = (Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d + 1)
    have hNatR : (Nat.card (subfaceCell O π (e' * d + 1) h e' d σ M) : ℝ)
          * ((residueCard O : ℕ) : ℝ) ^ (h * d + (wLeaf h e' d + 1))
        = (Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
          * ((residueCard O : ℕ) : ℝ) ^ ((e' * d + 1) * (M + (e' * d + 1))) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hNat
    have hp1 : ((residueCard O : ℕ) : ℝ) ^ ((e' * d + 1) * (M + (e' * d + 1))) ≠ 0 :=
      pow_ne_zero _ hqR
    have hp2 : ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d + 1) ≠ 0 :=
      pow_ne_zero _ hqR
    rw [div_eq_div_iff hp1 hp2]
    calc (Nat.card (subfaceCell O π (e' * d + 1) h e' d σ M) : ℝ)
          * ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d + 1)
        = (Nat.card (subfaceCell O π (e' * d + 1) h e' d σ M) : ℝ)
          * ((residueCard O : ℕ) : ℝ) ^ (h * d + (wLeaf h e' d + 1)) := by
          rw [show wLeaf h e' d + h * d + 1 = h * d + (wLeaf h e' d + 1) from by omega]
      _ = (Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
          * ((residueCard O : ℕ) : ℝ) ^ ((e' * d + 1) * (M + (e' * d + 1))) := hNatR
  · -- the mismatched type: the cell is empty at every level
    refine ZcURLim_zero.congr ?_
    intro O _ _ _ _ _ π hπ M
    have hempty := subfaceCell_r_one_empty hπ hh1 hhe hcop hd0' hσc M
    show (0 : ℝ) = (Nat.card (subfaceCell O π (e' * d + 1) h e' d σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((e' * d + 1) * (M + (e' * d + 1)))
    rw [hempty]
    simp

end Law

/-! ## §8 — ★ THE WITNESS FIRES and THE MASTERS RECOMPUTED: the leaf row's
remaining premise is the r ≥ 2 frames only -/

section Witness

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★★ **THE FIRST NON-SINGLETON LEAF LAW**: at LSC's hand-checked witness
`m = 5`, `σ = ⟨{(4,1), (1,1)}⟩`, both admissible frames `(1,4,1)` and `(3,4,1)`
have r = 1 — the leaf sub-face row CLOSES at the witness, machine-checked
end-to-end. -/
theorem leafSubfaceLaw_five : LeafSubfaceLaw 5 ⟨{(4, 1), (1, 1)}⟩ := by
  refine leafSubfaceLaw_of_frameLaws (by omega) _ fun p hp => ?_
  rw [subFrames_five_witness] at hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact subfaceFrameLaw_r_one 5 1 4 1 _ (by omega) (by omega) (by decide)
      (by omega) (by omega)
  · rw [Finset.mem_singleton] at hp
    subst hp
    exact subfaceFrameLaw_r_one 5 3 4 1 _ (by omega) (by omega) (by decide)
      (by omega) (by omega)

/-- ★★ **The frame family from the r ≥ 2 remainder**: the full per-frame family
follows from the laws at the frames with `m ≠ e'·d + 1` alone — the r = 1 members
are this file's theorem. -/
theorem subfaceFrameLaws_of_r_two (m : ℕ) (σ : FactorizationType)
    (hframe2 : ∀ p ∈ subFrames m σ, m ≠ p.2.1 * p.2.2 + 1 →
      SubfaceFrameLaw m p.1 p.2.1 p.2.2 σ) :
    ∀ p ∈ subFrames m σ, SubfaceFrameLaw m p.1 p.2.1 p.2.2 σ := by
  intro p hp
  obtain ⟨hh1, hhe, hcop, hd1, hdm, hmem⟩ := mem_subFrames_iff.mp hp
  by_cases heq : m = p.2.1 * p.2.2 + 1
  · exact subfaceFrameLaw_r_one m p.1 p.2.1 p.2.2 σ hh1 hhe hcop hd1 heq
  · exact hframe2 p hp heq

end Witness

/-! ## §9 — THE MASTERS RECOMPUTED: IFCG66's three spines with the leaf-row premise
demanded only at the r ≥ 2 frames (`e ≠ e'·d + 1`) -/

section Masters

open Uniformity.Density.IFCG66 (decidedSliceAt_all_of_visCensus_frames
  decidedSliceAt_all_of_MASTER_FRAMES capstoneHypotheses_of_MASTER_FRAMES)

/-- ★★★ **THE CENSUS MASTER ON PCD's SPINE, LEAF ROW ON r ≥ 2 FRAMES**. -/
theorem decidedSliceAt_all_of_visCensus_frames_r2
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
        ∀ p ∈ subFrames e σ, e ≠ p.2.1 * p.2.2 + 1 →
          SubfaceFrameLaw e p.1 p.2.1 p.2.2 σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_visCensus_frames hVC hPF
    (fun e he hsm σ hσ hwit hram hcard =>
      subfaceFrameLaws_of_r_two e σ (hFrame e he hsm σ hσ hwit hram hcard))
    hR4

/-- ★★★ **THE CENSUS MASTER ON LSC's SPINE, LEAF ROW ON r ≥ 2 FRAMES**: the
surviving premise surface is {`FactorCorrespondenceAt` (THE staged cite),
`EisFullSpanRemainderLaw`, `SplitConvolutionDefectLaw`, `PowerConvolutionDefectLaw`,
`SubfaceFrameLaw e h e' d σ` at the admissible frames with `e ≠ e'·d + 1`}. -/
theorem decidedSliceAt_all_of_MASTER_FRAMES_r2
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
        ∀ p ∈ subFrames e σ, e ≠ p.2.1 * p.2.2 + 1 →
          SubfaceFrameLaw e p.1 p.2.1 p.2.2 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_MASTER_FRAMES hFC hEis hSD hPD
    (fun e he hsm σ hσ hwit hram hcard =>
      subfaceFrameLaws_of_r_two e σ (hFrame e he hsm σ hσ hwit hram hcard))

universe uW uG uKt uL

/-- ★★★ **THE CAPSTONE MASTER, LEAF ROW ON r ≥ 2 FRAMES** (ID12's honesty frame
applies verbatim). -/
theorem capstoneHypotheses_of_MASTER_FRAMES_r2 (n : ℕ)
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
        ∀ p ∈ subFrames e σ, e ≠ p.2.1 * p.2.2 + 1 →
          SubfaceFrameLaw e p.1 p.2.1 p.2.2 σ) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  capstoneHypotheses_of_MASTER_FRAMES.{uW, uG, uKt, uL} n
    hladder hdeepTwist hFC hEis hSD hPD
    (fun e he hsm σ hσ hwit hram hcard =>
      subfaceFrameLaws_of_r_two e σ (hFrame e he hsm σ hσ hwit hram hcard))

end Masters

end Uniformity.Density.IFCG69

end

/-! ## AXCHECK FOOTER — expected: `card_steepLin`, `card_pinnedBox`,
`nzPoly_eval_card`, and `decidedAt_linear` are pure Lean core
`{propext, Classical.choice, Quot.sound}`; everything consuming LSF's transport or
LSC's bridge (`mul_mem_subfaceCell`, `subfaceCell_factors`, `subfaceCell_r_one_empty`,
`subfaceFrameLaw_r_one`, `leafSubfaceLaw_five`, `subfaceFrameLaws_of_r_two`, the two
census masters) is Lean core + EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited through
IFCG66/IFCG67 — never re-consumed); the capstone master additionally inherits
exactly `Uniformity.Density.Tower.agnprw_termination` (ID12's, previously declared).
The C.33 cites, `AX_cellRecursion`, and `sorryAx` must NOT occur. -/

#print axioms Uniformity.Density.IFCG69.card_steepLin
#print axioms Uniformity.Density.IFCG69.card_pinnedBox
#print axioms Uniformity.Density.IFCG69.nzPoly_eval_card
#print axioms Uniformity.Density.IFCG69.decidedAt_linear
#print axioms Uniformity.Density.IFCG69.mul_mem_subfaceCell
#print axioms Uniformity.Density.IFCG69.subfaceCell_factors
#print axioms Uniformity.Density.IFCG69.subfaceCell_r_one_empty
#print axioms Uniformity.Density.IFCG69.subfaceFrameLaw_r_one
#print axioms Uniformity.Density.IFCG69.leafSubfaceLaw_five
#print axioms Uniformity.Density.IFCG69.subfaceFrameLaws_of_r_two
#print axioms Uniformity.Density.IFCG69.decidedSliceAt_all_of_visCensus_frames_r2
#print axioms Uniformity.Density.IFCG69.decidedSliceAt_all_of_MASTER_FRAMES_r2
#print axioms Uniformity.Density.IFCG69.capstoneHypotheses_of_MASTER_FRAMES_r2
