/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG69

/-!
# Uniformity.ChapI.IFCG72 — [R2F 2026-08-31] the r ≥ 2 sub-face frames: the general
fiber through the Bezout gap engine, the steep census reduction, and the conditional
frame laws

Stage R2F of the cone census (design record `runs/wave-c/verdict_R2F.md`; consumes
SFW = `IFCG69`, DPN = `IFCG67`, LSF = `IFCG66`, and the gap/Bezout machinery of
`IFCG41`/`IFCG42`).  SFW closed every r = 1 frame unconditionally; this file attacks
the honest r ≥ 2 remainder:

* **§1 THE CARRIERS**: `steepCone` (the strict-cone digit box at cofactor mass `r` —
  LSF's steepness seed, matching DPN's coupling hypotheses on the nose) and
  `steepDecCensus` (the cone ∩ the decided-`τ` classes at the SAME window — the honest
  census carrier).  `SteepDecCensusLaw r h e' τ` names its `ZcURLim`.
* **§2 ★ THE EXACT UNIQUENESS ENGINE** (`exact_factorization_unique`, any commutative
  domain, splitting-field-free): two exact monic factorizations of one polynomial with
  nonvanishing CROSS resultant are equal — the Bezout witness collapses the difference
  by degrees.  This is the missing exact leg of the r ≥ 2 separation.
* **§3–§6 THE PRODUCT PACKAGE AT GENERAL r**: the convolution cone bounds with the
  EXACT coordinate `h·d` at abscissa `r` and the strictly-raised corner; the face
  package at mass `m = e'·d + r`; the residual factorization (the steep side residual
  is a unit — the strict cone collapses the side to the monic point); the box
  decidedness at the shifted window `K − h·d·r`.
* **§7–§8 THE IMAGE AND THE SURJECTION**: (pinned box) × (steep census) lands in
  `subfaceCell`; every cell factors through (pinned box) × (steep cone), the type is
  forced (`σ.data = (e',d) ::ₘ τ.data`), and — THE DRAINAGE DISSOLUTION — the steep
  factor class is decided-`τ` at the FULL window, pointwise, by `typeOf_mul` + the
  box's forced type + multiset cons-cancellation.  LSF's fence 2 (shifted-level factor
  decidedness) is NOT needed anywhere in this file.
* **§9 ★★ THE GENERAL FIBER**: over every cell point, the `mulClass` fiber inside
  (pinned box) ×ˢ (steep cone) is EXACTLY one `pairNbhd` cluster at DPN's pinned depth
  `v = h·d·(m − e'·d)`, hence of size `q^v` — separation by
  `liftsFactor_of_not_dvd_resultant` (the Hensel leg at the Bezout depth from DPN's
  strict resultant half) + §2's exact uniqueness at the MIXED pair; stability because
  every geometric read lives at digit levels ≤ v.
* **§10 ★★★ THE CONDITIONAL LAW**: the count SQUEEZE
  `#box·q^{rv}·#census(K−v) ≤ #cell·q^v ≤ #box·#census(K)` closes the frame law from
  the census law alone: `SteepDecCensusLaw (m−e'd) h e' ⟨σ.data.erase (e',d)⟩ →
  SubfaceFrameLaw m h e' d σ` at EVERY r ≥ 1 frame — value
  `nz_d(q)·L_τ(q)/q^{wLeaf + h·d·r}`.
* **§11 THE MASTERS**: the three spines with the leaf row's r ≥ 2 premise re-based
  from `SubfaceFrameLaw` onto the strictly finer census family.

## Honest scope

NOT proved here (the exact named remainder): `SteepDecCensusLaw r h e' τ` at the
NON-special r ≥ 2 frames — the steep decided census value at genuinely fractional
boxes.  The anticipated product value `q^{−wSteep}·decidedDensity(r,τ)` is REFUTED
(design record, Finding A: at `h/e' = 1/2`, `r = 3`, `τ = {(3,1)}` the boxed decided
density alone exceeds `q^{−wSteep}`), so the census does NOT factor off the < e
value laws in general; it is a genuinely new census family.  AT THE SPECIAL FRAMES
`r·(e'−h) ≤ e'` the strict cone IS the integer slope-1 box and §14 CLOSES the census
from `DecidedValueLaw r τ` alone (`steepDecCensusLaw_of_special`), with the first
unconditional r = 2 member `subfaceFrameLaw_r_two_witness`.  Nothing is weakened:
`SubfaceFrameLaw`/`LeafSubfaceLaw`/the master statements are byte-untouched upstream;
the masters below refine IFCG69's by the discharge-path re-base idiom (LSF §4's
sanctioned genre).

## Axiom fence (expected at landing)

§1's carriers and counts, §2, and the §9 fiber engine are pure Lean core
`{propext, Classical.choice, Quot.sound}`; everything consuming LSF's transport
(§7 §8 §10 §11) inherits Lean core + EXACTLY the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42, through IFCG66/67/69 —
never re-consumed); the capstone master additionally inherits
`Uniformity.Density.Tower.agnprw_termination` (ID12's, previously declared).  The
C.33 cites, `AX_cellRecursion`, and `sorryAx` must NOT occur.  Zero sorries at
landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG72

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
  le_classCoeffVal_iff_dvd classCoeffVal_exact classCoeffVal_le resOrd_mk_eq)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq)
open Uniformity.Density.IFCG3 (bigTLoop kappaLoop bigTLoop_eq_kappaLoop_add
  kappaLoop_eq_sum scaleVecN monicPoly_scaleVecN_eq_scaleRoots typeOf_scaleVecN)
open Uniformity.Density.IFCG24 (npHeight_coe ZcURLim ZcURLim_zero ZcURLim_sum
  ConeRemainderLaw shallowSet pureFaceSet faceBox faceH mem_stratum_X_pow_iff
  card_setOf_le_resOrd card_pi_set)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains mem_sideSet_of_onSide)
open Uniformity.Density.IFCG28 (classSideSet sideSet_monicPoly_eq sideMin_monicPoly_eq
  sideMax_monicPoly_eq)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_unique classResidualPoly
  classResidualPoly_eq)
open Uniformity.Density.IFCG36 (resDig resDig_mk resOrd_eq_iff_resDig card_setOf_resDig)
open Uniformity.Density.IFCG37 (decidedAt_of_spanning_irr)
open Uniformity.Density.IFCG38 (SplitConvolutionDefectLaw)
open Uniformity.Density.IFCG41 (LiftsFactor)
open Uniformity.Density.IFCG42 (pairNbhd liftsFactor_of_not_dvd_resultant)
open Uniformity.Density.IFCG44 (PowerConvolutionDefectLaw PowerFullSpanLaw)
open Uniformity.Density.IFCG46 (card_preimage_coeffFactor_eq)
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
  decidedAt_mulClass_of_cones not_pow_succ_dvd_resultant_of_cones)
open Uniformity.Density.IFCG69 (pinnedBox nzGenre nzPoly finite_nzGenre
  card_pinnedBox card_steepLin nzPoly_eval_card subfaceFrameLaw_r_one
  steepLin decidedAt_linear)

attribute [local instance] Classical.propDecidable

/-! ## §0 — kit (private replicas of the established supply) -/

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

/-- The pinned-box lift divisibility bank (SFW's private replica): the threshold
divisibilities and the exact corner pair, on any lift of pinned-box data. -/
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

end Kit

/-! ## §1 — the steep carriers at cofactor mass r and the census law -/

section Carriers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The steep threshold**: the least `t` with `h·(r − j) < e'·t` — the digit floor of
the strict cone at abscissa `j`. -/
def tSteep (h e' r j : ℕ) : ℕ := h * (r - j) / e' + 1

/-- The defining dictionary of the steep threshold. -/
theorem tSteep_le_iff {e' : ℕ} (he' : 0 < e') (h r j t : ℕ) :
    tSteep h e' r j ≤ t ↔ h * (r - j) < e' * t := by
  unfold tSteep
  have hcomm : t * e' = e' * t := Nat.mul_comm t e'
  constructor
  · intro h1
    have h2 : h * (r - j) / e' < t := by omega
    have h3 : h * (r - j) < t * e' := (Nat.div_lt_iff_lt_mul he').mp h2
    omega
  · intro h1
    have h2 : h * (r - j) < t * e' := by omega
    have h3 : h * (r - j) / e' < t := (Nat.div_lt_iff_lt_mul he').mpr h2
    omega

/-- The steep threshold is capped by the mass: `tSteep ≤ r` under `h < e'`. -/
theorem tSteep_le_mass {h e' : ℕ} (hh : 0 < h) (hhe : h < e') (r j : ℕ) (hr : 0 < r) :
    tSteep h e' r j ≤ r := by
  refine (tSteep_le_iff (by omega) h r j r).mpr ?_
  have h1 : h * (r - j) ≤ h * r := Nat.mul_le_mul_left h (Nat.sub_le _ _)
  have h2 : h * r < e' * r := Nat.mul_lt_mul_of_lt_of_le hhe (le_refl r) hr
  omega

/-- **The steep cone at mass `r`** (the strict-cone digit box — LSF's steepness seed,
in exactly DPN's coupling shape). -/
def steepCone (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (r K h e' : ℕ) : Set (Coeff O r K) :=
  {ρ | ∀ j : Fin r, h * (r - (j : ℕ)) < e' * resOrd (ρ j)}

/-- **The steep decided census carrier**: the strict cone ∩ the decided-`τ` classes,
at ONE window.  Its normalized limit is THE honest open engine of the r ≥ 2 frames. -/
def steepDecCensus (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (r K h e' : ℕ) (τ : FactorizationType) :
    Set (Coeff O r K) :=
  {ρ | ρ ∈ steepCone O r K h e' ∧ DecidedAt O r τ K ρ}

/-- ★ **THE STEEP DECIDED CENSUS LAW** (the named remainder of the r ≥ 2 frames): one
uniform rational pair for the normalized steep decided census.  At `r = 1` it is SFW's
exact count; at r ≥ 2 it is open (the design record refutes the naive product value). -/
def SteepDecCensusLaw (r h e' : ℕ) (τ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ _ M =>
    (Nat.card (steepDecCensus O r (M + r) h e' τ) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (r * (M + r)))

end Carriers

/-! ## §2 — ★ THE EXACT UNIQUENESS ENGINE (splitting-field-free, any commutative
domain): two exact monic factorizations with nonvanishing cross resultant agree -/

section ExactUnique

variable {O : Type*} [CommRing O] [IsDomain O]

/-- ★ **EXACT FACTORIZATION UNIQUENESS**: if `W₁·W₂ = B₁·B₂` with all four monic,
`deg B₁ = deg W₁`, `deg B₂ = deg W₂`, and the CROSS resultant `Res(W₁, B₂)` does not
vanish, then `B₁ = W₁` and `B₂ = W₂`.  Mechanism: the Bezout row of the Sylvester
adjugate gives `W₁·p + B₂·q = C(Res)`; multiplying by `D := B₁ − W₁` and substituting
the product identity `D·B₂ = −W₁·(B₂ − W₂)` yields `W₁·(p·D − q·E) = C(Res)·D`, which
forces `D = 0` by degrees.  No splitting fields, no completeness, no valuation. -/
theorem exact_factorization_unique {W₁ W₂ B₁ B₂ : Polynomial O}
    (hW₁ : W₁.Monic) (hB₁ : B₁.Monic)
    (hd₁ : B₁.natDegree = W₁.natDegree)
    (hpos : W₁.natDegree ≠ 0 ∨ B₂.natDegree ≠ 0)
    (heq : W₁ * W₂ = B₁ * B₂)
    (hres : Polynomial.resultant W₁ B₂ W₁.natDegree B₂.natDegree ≠ 0) :
    B₁ = W₁ ∧ B₂ = W₂ := by
  obtain ⟨p, q, hp, hq, hkey⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant W₁ B₂ le_rfl le_rfl hpos
  set D : Polynomial O := B₁ - W₁ with hD
  set E : Polynomial O := B₂ - W₂ with hE
  -- the product identity: D·B₂ = −W₁·E
  have hDB : D * B₂ = -(W₁ * E) := by
    have h1 : D * B₂ = B₁ * B₂ - W₁ * B₂ := by rw [hD]; ring
    rw [h1, ← heq, hE]
    ring
  -- the Bezout collapse: C(Res)·D = W₁·(p·D − q·E)
  have hmain : Polynomial.C (Polynomial.resultant W₁ B₂ W₁.natDegree B₂.natDegree) * D
      = W₁ * (p * D - q * E) :=
    calc Polynomial.C (Polynomial.resultant W₁ B₂ W₁.natDegree B₂.natDegree) * D
        = (W₁ * p + B₂ * q) * D := by rw [hkey]
      _ = W₁ * (p * D) + (D * B₂) * q := by ring
      _ = W₁ * (p * D) + (-(W₁ * E)) * q := by rw [hDB]
      _ = W₁ * (p * D - q * E) := by ring
  by_cases hD0 : D = 0
  · -- B₁ = W₁; the cofactor follows by monic cancellation
    have hB₁W : B₁ = W₁ := by
      have h0 : B₁ - W₁ = 0 := hD0
      rwa [sub_eq_zero] at h0
    refine ⟨hB₁W, ?_⟩
    have h2 : W₁ * W₂ = W₁ * B₂ := by
      rw [heq, hB₁W]
    exact (mul_left_cancel₀ hW₁.ne_zero h2).symm
  · -- D ≠ 0 is impossible by degrees
    exfalso
    have hCne : (Polynomial.C (Polynomial.resultant W₁ B₂ W₁.natDegree B₂.natDegree)
        : Polynomial O) ≠ 0 := by
      simpa using hres
    have hRHSne : Polynomial.C (Polynomial.resultant W₁ B₂ W₁.natDegree B₂.natDegree)
        * D ≠ 0 := mul_ne_zero hCne hD0
    have hpq : p * D - q * E ≠ 0 := by
      intro h0
      rw [hmain, h0, mul_zero] at hRHSne
      exact hRHSne rfl
    have hdegL : (Polynomial.C (Polynomial.resultant W₁ B₂ W₁.natDegree B₂.natDegree)
        * D).degree = D.degree := by
      rw [Polynomial.degree_mul, Polynomial.degree_C hres, zero_add]
    have hdegD : D.degree < W₁.degree := by
      have hdeq : B₁.degree = W₁.degree := by
        rw [Polynomial.degree_eq_natDegree hB₁.ne_zero,
          Polynomial.degree_eq_natDegree hW₁.ne_zero, hd₁]
      have h1 := Polynomial.degree_sub_lt hdeq hB₁.ne_zero
        (by rw [hB₁.leadingCoeff, hW₁.leadingCoeff])
      rwa [hdeq] at h1
    have hcontra : W₁.degree ≤ D.degree := by
      rw [← hdegL, hmain, Polynomial.degree_mul]
      have h1 : (0 : WithBot ℕ) ≤ (p * D - q * E).degree :=
        Polynomial.zero_le_degree_iff.mpr hpq
      exact le_add_of_nonneg_right h1
    exact absurd hdegD (not_lt.mpr hcontra)

end ExactUnique

/-! ## §3 — ★★ THE GENERAL FIBER: over every carrier product, the `mulClass` fiber
inside (pinned box) ×ˢ (steep cone) is EXACTLY one `pairNbhd` cluster at the pinned
depth `v = h·d·r` -/

section Fiber

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The steep lift divisibility bank: `π^{tSteep j} ∣ a₂ j` on any lift of steep-cone
data. -/
private theorem steep_lift_divs {π : O} (hπ : Irreducible π) {h e' r : ℕ}
    (hh : 0 < h) (hhe : h < e') {K : ℕ}
    {a₂ : Fin r → O} (hst : proj O r K a₂ ∈ steepCone O r K h e') :
    ∀ j : Fin r, π ^ (tSteep h e' r (j : ℕ)) ∣ a₂ j := by
  intro j
  have h1 : tSteep h e' r (j : ℕ) ≤ resOrd (proj O r K a₂ j) :=
    (tSteep_le_iff (by omega) h r (j : ℕ) _).mpr (hst j)
  have h2 : π ^ (resOrd (proj O r K a₂ j)) ∣ a₂ j :=
    (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
  exact (pow_dvd_pow π h1).trans h2

/-- The steep cone is stable under `π^r`-perturbation of the lift (every steep read
lives at digit levels ≤ tSteep ≤ r). -/
private theorem steepCone_stable {π : O} (hπ : Irreducible π) {h e' r : ℕ}
    (hh : 0 < h) (hhe : h < e') (hr : 0 < r) {K : ℕ} (hrK : r ≤ K)
    {a₂ b₂ : Fin r → O} (hst : proj O r K a₂ ∈ steepCone O r K h e')
    (hcong : ∀ i, π ^ r ∣ b₂ i - a₂ i) :
    proj O r K b₂ ∈ steepCone O r K h e' := by
  intro j
  have hts : tSteep h e' r (j : ℕ) ≤ r := tSteep_le_mass hh hhe r _ hr
  have h1 : π ^ (tSteep h e' r (j : ℕ)) ∣ b₂ j := by
    have h2 : b₂ j = a₂ j + (b₂ j - a₂ j) := by ring
    rw [h2]
    exact dvd_add (steep_lift_divs hπ hh hhe hst j)
      ((pow_dvd_pow π hts).trans (hcong j))
  have h3 : tSteep h e' r (j : ℕ) ≤ resOrd (proj O r K b₂ j) :=
    (le_classCoeffVal_iff_dvd hπ (by omega : tSteep h e' r (j : ℕ) ≤ K) rfl j).mpr h1
  exact (tSteep_le_iff (by omega) h r (j : ℕ) _).mp h3

/-- The pinned box is stable under `π^{h·d+1}`-perturbation of the lift (every box
read lives at digit levels ≤ h·d). -/
private theorem pinnedBox_stable {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) {K : ℕ} (hhdK : h * d < K)
    {a₁ b₁ : Fin (e' * d) → O}
    (ha : proj O (e' * d) K a₁ ∈ pinnedBox π K h e' d)
    (hcong : ∀ i, π ^ (h * d + 1) ∣ b₁ i - a₁ i) :
    proj O (e' * d) K b₁ ∈ pinnedBox π K h e' d := by
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  obtain ⟨hcone, hcorner, hirr⟩ := ha
  obtain ⟨hL2a, hL1a⟩ := box_lift_divs hπ hh hhe hd0 hhdK hcone hcorner
  have hb₁divs : ∀ j : Fin (e' * d), π ^ (tLeaf h e' (e' * d) (j : ℕ)) ∣ b₁ j := by
    intro j
    have h1 : b₁ j = a₁ j + (b₁ j - a₁ j) := by ring
    rw [h1]
    refine dvd_add (hL2a j) ?_
    have h2 : tLeaf h e' (e' * d) (j : ℕ) ≤ h * d + 1 := by
      have := tLeaf_le_corner he'0 h d (j : ℕ)
      omega
    exact (pow_dvd_pow π h2).trans (hcong j)
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
    exact dvd_add ha0dvd ((pow_dvd_pow π (by omega)).trans (hcong ⟨0, hn0⟩))
  have hb0ndvd : ¬ π ^ (h * d + 1) ∣ b₁ ⟨0, hn0⟩ := by
    intro hcon
    refine ha0ndvd ?_
    have h1 : a₁ ⟨0, hn0⟩ = b₁ ⟨0, hn0⟩ - (b₁ ⟨0, hn0⟩ - a₁ ⟨0, hn0⟩) := by ring
    rw [h1]
    exact dvd_sub hcon (hcong ⟨0, hn0⟩)
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
    refine digAt_congr hπ ?_ (hcong ⟨e' * k, hek⟩)
    have h1 : h * (d - k) ≤ h * d := Nat.mul_le_mul_left h (Nat.sub_le _ _)
    omega
  exact ⟨hconeB, hcornerB, by rw [hdigB]; exact hirr⟩

/-- ★★ **THE GENERAL FIBER IS ONE CLUSTER** (the r ≥ 2 separation engine, charge
item 1): over the product class of a carrier pair, the `mulClass` fiber inside
(pinned box) ×ˢ (steep cone) is EXACTLY the depth-`h·d·r` pair neighborhood — hence
of size `q^{h·d·r}` by DPN's fiber law.  Separation (⊆): the Hensel leg
(`liftsFactor_of_not_dvd_resultant` at the Bezout depth pinned by DPN's strict
determinant half) refactors the exact product `W₁·W₂` through the base pair mod
`π^{v+1}`, and the exact-uniqueness engine at the MIXED pair `(W₁, B₂)` — whose
resultant is nonvanishing by the same strict half, since the perturbed steep side
keeps its strict cone — collapses the two exact factorizations, so the carrier pair
IS the Hensel pair.  Stability (⊇): every box/steep read lives at digit levels
≤ h·d < v + 1 resp. ≤ r ≤ v + 1. -/
theorem fiber_eq_pairNbhd_gen [IsAdicComplete (maximalIdeal O) O] {π : O}
    (hπ : Irreducible π) {h e' d r : ℕ}
    (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) (hr : 0 < r)
    {K : ℕ} (hK2 : 2 * (h * d * r) + 1 ≤ K)
    {a₁ : Fin (e' * d) → O} {a₂ : Fin r → O}
    (hbox : proj O (e' * d) K a₁ ∈ pinnedBox π K h e' d)
    (hsteep : proj O r K a₂ ∈ steepCone O r K h e') :
    (pinnedBox π K h e' d ×ˢ steepCone O r K h e')
        ∩ (fun p : Coeff O (e' * d) K × Coeff O r K => mulClass p.1 p.2) ⁻¹'
            {mulClass (proj O (e' * d) K a₁) (proj O r K a₂)}
      = pairNbhd π K (h * d * r) a₁ a₂ := by
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hhdv : h * d ≤ h * d * r := Nat.le_mul_of_pos_right _ hr
  have hrv : r ≤ h * d * r := by
    have h1 : 1 ≤ h * d := Nat.mul_pos hh hd0
    have h2 : 1 * r ≤ (h * d) * r := Nat.mul_le_mul_right r h1
    omega
  have hhdK : h * d < K := by omega
  have hrK : r ≤ K := by omega
  obtain ⟨hcone, hcorner, hirr⟩ := hbox
  -- the base Bezout depth: DPN's strict determinant half at the base pair
  have hbez : ¬ π ^ (h * d * r + 1)
      ∣ Polynomial.resultant (monicPoly a₁) (monicPoly a₂) (e' * d) r := by
    have hd₁ : ∀ j, π ^ (resOrd (proj O (e' * d) K a₁ j)) ∣ a₁ j := fun j =>
      (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
    have hd₂ : ∀ j, π ^ (resOrd (proj O r K a₂ j)) ∣ a₂ j := fun j =>
      (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
    have hu : h * (e' * d) = e' * (h * d) := by ring
    obtain ⟨-, hndc⟩ := (box_lift_divs hπ hh hhe hd0 hhdK hcone hcorner).2 ⟨0, hn0⟩ rfl
    exact not_pow_succ_dvd_resultant_of_cones hπ.prime he'0 hn0 hu hd₁ hd₂
      (fun j => hcone j) (fun j => by have := hsteep j; omega) hndc
  have hLF : LiftsFactor π (h * d * r) K a₁ a₂ :=
    liftsFactor_of_not_dvd_resultant hπ (by omega) (Or.inl (by omega)) hbez
  ext ⟨c₁, c₂⟩
  simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · -- SEPARATION
    rintro ⟨⟨hc₁, hc₂⟩, hpre⟩
    obtain ⟨w₁, rfl⟩ := proj_surjective O (e' * d) K c₁
    obtain ⟨w₂, rfl⟩ := proj_surjective O r K c₂
    -- the exact product lifts the base product class
    have hFproj : proj O (e' * d + r) K
        (fun i => (monicPoly w₁ * monicPoly w₂).coeff (i : ℕ))
        = mulClass (proj O (e' * d) K a₁) (proj O r K a₂) := by
      rw [mulClass_proj]
      exact hpre
    obtain ⟨b₁, b₂, hfac, hcb₁, hcb₂⟩ := hLF _ hFproj
    have hWm : (monicPoly w₁ * monicPoly w₂).Monic :=
      (monicPoly_monic w₁).mul (monicPoly_monic w₂)
    have hWdeg : (monicPoly w₁ * monicPoly w₂).natDegree = e' * d + r := by
      rw [(monicPoly_monic w₁).natDegree_mul (monicPoly_monic w₂),
        monicPoly_natDegree, monicPoly_natDegree]
    have hmpF : monicPoly (fun i : Fin (e' * d + r) =>
        (monicPoly w₁ * monicPoly w₂).coeff (i : ℕ)) = monicPoly w₁ * monicPoly w₂ :=
      monicPoly_coeff_eq_self hWm hWdeg
    rw [hmpF] at hfac
    -- the perturbed steep side keeps the strict cone
    have hstb₂ : proj O r K b₂ ∈ steepCone O r K h e' :=
      steepCone_stable hπ hh hhe hr hrK hsteep
        (fun i => (pow_dvd_pow π (by omega : r ≤ h * d * r + 1)).trans (hcb₂ i))
    -- the MIXED resultant does not vanish (the strict half again)
    have hmixed : Polynomial.resultant (monicPoly w₁) (monicPoly b₂) (e' * d) r ≠ 0 := by
      obtain ⟨hconeW, hcornerW, -⟩ := hc₁
      have hd₁ : ∀ j, π ^ (resOrd (proj O (e' * d) K w₁ j)) ∣ w₁ j := fun j =>
        (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
      have hd₂ : ∀ j, π ^ (resOrd (proj O r K b₂ j)) ∣ b₂ j := fun j =>
        (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
      have hu : h * (e' * d) = e' * (h * d) := by ring
      obtain ⟨-, hndc⟩ :=
        (box_lift_divs hπ hh hhe hd0 hhdK hconeW hcornerW).2 ⟨0, hn0⟩ rfl
      intro h0
      refine not_pow_succ_dvd_resultant_of_cones hπ.prime he'0 hn0 hu hd₁ hd₂
        (fun j => hconeW j) (fun j => by have := hstb₂ j; omega) hndc ?_
      rw [h0]
      exact dvd_zero _
    -- exact uniqueness at the mixed pair: the carrier pair IS the Hensel pair
    have hresW : Polynomial.resultant (monicPoly w₁) (monicPoly b₂)
        (monicPoly w₁).natDegree (monicPoly b₂).natDegree ≠ 0 := by
      rw [monicPoly_natDegree, monicPoly_natDegree]
      exact hmixed
    have hposW : (monicPoly w₁).natDegree ≠ 0 ∨ (monicPoly b₂).natDegree ≠ 0 := by
      left
      rw [monicPoly_natDegree]
      omega
    have hdeq : (monicPoly b₁).natDegree = (monicPoly w₁).natDegree := by
      rw [monicPoly_natDegree, monicPoly_natDegree]
    obtain ⟨hB₁W, hB₂W⟩ := exact_factorization_unique (monicPoly_monic w₁)
      (monicPoly_monic b₁) hdeq hposW hfac hresW
    have hw₁b : ∀ i : Fin (e' * d), w₁ i = b₁ i := by
      intro i
      have h1 := congrArg (fun p : Polynomial O => p.coeff (i : ℕ)) hB₁W
      simpa [monicPoly_coeff_lt b₁ i.isLt, monicPoly_coeff_lt w₁ i.isLt] using h1.symm
    have hw₂b : ∀ i : Fin r, w₂ i = b₂ i := by
      intro i
      have h1 := congrArg (fun p : Polynomial O => p.coeff (i : ℕ)) hB₂W
      simpa [monicPoly_coeff_lt b₂ i.isLt, monicPoly_coeff_lt w₂ i.isLt] using h1.symm
    exact ⟨hpre, ⟨w₁, rfl, fun i => by rw [hw₁b i]; exact hcb₁ i⟩,
      ⟨w₂, rfl, fun i => by rw [hw₂b i]; exact hcb₂ i⟩⟩
  · -- STABILITY
    rintro ⟨hpre, ⟨b₁, rfl, hcong₁⟩, ⟨b₂, rfl, hcong₂⟩⟩
    refine ⟨⟨?_, ?_⟩, hpre⟩
    · exact pinnedBox_stable hπ hh hhe hd0 hhdK ⟨hcone, hcorner, hirr⟩
        (fun i => (pow_dvd_pow π (by omega : h * d + 1 ≤ h * d * r + 1)).trans (hcong₁ i))
    · exact steepCone_stable hπ hh hhe hr hrK hsteep
        (fun i => (pow_dvd_pow π (by omega : r ≤ h * d * r + 1)).trans (hcong₂ i))

end Fiber

/-! ## §4 — THE PRODUCT PACKAGE at general r, part 1: the coefficient data
(the convolution cone bounds with the EXACT coordinate at abscissa `r`) -/

section ProductData

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The thresholds are antitone in the abscissa (SFW's private replica). -/
private theorem tLeaf_antitone (h e' m : ℕ) {i j : ℕ} (hij : i ≤ j) :
    tLeaf h e' m j ≤ tLeaf h e' m i := by
  unfold tLeaf
  exact Nat.div_le_div_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left h (by omega)) _)

/-- The corner threshold of the block: `h·d ≤ tLeaf (e'·d) 0`. -/
private theorem hd_le_tLeaf_zero {h e' d : ℕ} (hh : 0 < h) (hhe : h < e') :
    h * d ≤ tLeaf h e' (e' * d) 0 := by
  have he'0 : 0 < e' := by omega
  have h1 : h * (e' * d - 0) ≤ e' * tLeaf h e' (e' * d) 0 :=
    (tLeaf_le_iff he'0 h (e' * d) 0 _).mp le_rfl
  have h2 : h * (e' * d) = e' * (h * d) := by ring
  simp only [Nat.sub_zero] at h1
  refine Nat.le_of_mul_le_mul_left ?_ he'0
  omega

/-- **The convolution divisibility engine**: a product coefficient inherits `π^T`
whenever `T` is beaten by every antidiagonal term's threshold sum (interior terms:
`tLeaf + tSteep`; the two monic tops: the partner's threshold alone). -/
private theorem prod_coeff_dvd {π : O} {h e' d r : ℕ}
    {a₁ : Fin (e' * d) → O} {a₂ : Fin r → O}
    (hL : ∀ j : Fin (e' * d), π ^ (tLeaf h e' (e' * d) (j : ℕ)) ∣ a₁ j)
    (hS : ∀ j : Fin r, π ^ (tSteep h e' r (j : ℕ)) ∣ a₂ j)
    (T : ℕ) (j : ℕ) (hj : j < e' * d + r)
    (hbound₁ : ∀ (i : Fin (e' * d)) (k : Fin r), (i : ℕ) + (k : ℕ) = j →
      T ≤ tLeaf h e' (e' * d) (i : ℕ) + tSteep h e' r (k : ℕ))
    (hbound₂ : ∀ k : Fin r, e' * d + (k : ℕ) = j → T ≤ tSteep h e' r (k : ℕ))
    (hbound₃ : ∀ i : Fin (e' * d), (i : ℕ) + r = j → T ≤ tLeaf h e' (e' * d) (i : ℕ)) :
    π ^ T ∣ (monicPoly a₁ * monicPoly a₂).coeff j := by
  rw [Polynomial.coeff_mul]
  refine Finset.dvd_sum fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rcases Nat.lt_or_ge x.1 (e' * d) with hi | hi
  · rcases Nat.lt_or_ge x.2 r with hk | hk
    · -- both interior
      rw [monicPoly_coeff_lt a₁ hi, monicPoly_coeff_lt a₂ hk]
      have h1 := mul_dvd_mul (hL ⟨x.1, hi⟩) (hS ⟨x.2, hk⟩)
      rw [← pow_add] at h1
      exact (pow_dvd_pow π (hbound₁ ⟨x.1, hi⟩ ⟨x.2, hk⟩ hx)).trans h1
    · rcases Nat.eq_or_lt_of_le hk with hk' | hk'
      · -- the steep monic top
        have htop : (monicPoly a₂).coeff x.2 = 1 := by
          rw [← hk']
          have h1 := (monicPoly_monic a₂).coeff_natDegree
          rwa [monicPoly_natDegree] at h1
        rw [monicPoly_coeff_lt a₁ hi, htop, mul_one]
        exact (pow_dvd_pow π (hbound₃ ⟨x.1, hi⟩ (by show x.1 + r = j; omega))).trans
          (hL ⟨x.1, hi⟩)
      · have hz : (monicPoly a₂).coeff x.2 = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (by rw [monicPoly_natDegree]; exact hk')
        rw [hz, mul_zero]
        exact dvd_zero _
  · rcases Nat.eq_or_lt_of_le hi with hi' | hi'
    · rcases Nat.lt_or_ge x.2 r with hk | hk
      · -- the block monic top
        have htop : (monicPoly a₁).coeff x.1 = 1 := by
          rw [← hi']
          have h1 := (monicPoly_monic a₁).coeff_natDegree
          rwa [monicPoly_natDegree] at h1
        rw [htop, one_mul, monicPoly_coeff_lt a₂ hk]
        exact (pow_dvd_pow π (hbound₂ ⟨x.2, hk⟩ (by show e' * d + x.2 = j; omega))).trans
          (hS ⟨x.2, hk⟩)
      · -- both tops: j = e'd + r, excluded
        omega
    · have hz : (monicPoly a₁).coeff x.1 = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (by rw [monicPoly_natDegree]; exact hi')
      rw [hz, zero_mul]
      exact dvd_zero _

/-- **The product coefficient data at general r**: the class of `g·R` — `g` a
cone-with-exact-corner block, `R` steep of mass `r` — carries the frame cone at total
mass `e'd + r` with the EXACT coordinate `resOrd = h·d` at abscissa `r` and the
strictly-raised corner `e'·(h·d) + h·r < e'·resOrd` at abscissa `0`. -/
private theorem prod_class_data_gen {π : O} (hπ : Irreducible π) {h e' d r : ℕ}
    (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) (hr : 0 < r)
    {K : ℕ} (hK : h * d + tSteep h e' r 0 ≤ K)
    {a₁ : Fin (e' * d) → O} {a₂ : Fin r → O}
    (hcone : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) K a₁ j))
    (hcorner : resOrd (resAt (proj O (e' * d) K a₁) 0) = h * d)
    (hsteep : proj O r K a₂ ∈ steepCone O r K h e') :
    (∀ j : Fin (e' * d + r),
        h * ((e' * d + r) - (j : ℕ))
          ≤ e' * resOrd (proj O (e' * d + r) K
              (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) j))
      ∧ resOrd (resAt (proj O (e' * d + r) K
          (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) r) = h * d
      ∧ e' * (h * d) + h * r < e' * resOrd (resAt (proj O (e' * d + r) K
          (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) 0) := by
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hts1 : 0 < tSteep h e' r 0 := Nat.succ_le_succ (Nat.zero_le _)
  have hhdK : h * d < K := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hts1) hK
  -- the lift banks
  obtain ⟨hL2, hL1⟩ := box_lift_divs hπ hh hhe hd0 hhdK hcone hcorner
  have hS := steep_lift_divs hπ hh hhe hsteep
  obtain ⟨hc0dvd, hc0ndvd⟩ := hL1 ⟨0, hn0⟩ rfl
  -- the steep floor at the origin, cleared: `h·r < e'·tSteep 0`
  have hB0 : h * r < e' * tSteep h e' r 0 := by
    have h1 := (tSteep_le_iff he'0 h r 0 (tSteep h e' r 0)).mp le_rfl
    simpa using h1
  -- the cone cap: `tLeaf_m 0 ≤ h·d + tSteep 0 ≤ K`
  have hcap0 : tLeaf h e' (e' * d + r) 0 ≤ h * d + tSteep h e' r 0 := by
    refine (tLeaf_le_iff he'0 h (e' * d + r) 0 _).mpr ?_
    have h1 : h * (e' * d + r - 0) = e' * (h * d) + h * r := by
      rw [Nat.sub_zero, Nat.mul_add]
      ring_nf
    have h2 : e' * (h * d + tSteep h e' r 0)
        = e' * (h * d) + e' * tSteep h e' r 0 := Nat.mul_add e' _ _
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- THE CONE
    intro j
    have hdvd : π ^ (tLeaf h e' (e' * d + r) (j : ℕ))
        ∣ (monicPoly a₁ * monicPoly a₂).coeff (j : ℕ) := by
      refine prod_coeff_dvd hL2 hS _ (j : ℕ) j.isLt ?_ ?_ ?_
      · intro i k hik
        have hA : h * (e' * d - (i : ℕ)) ≤ e' * tLeaf h e' (e' * d) (i : ℕ) :=
          (tLeaf_le_iff he'0 h (e' * d) (i : ℕ) _).mp le_rfl
        have hB : h * (r - (k : ℕ)) < e' * tSteep h e' r (k : ℕ) :=
          (tSteep_le_iff he'0 h r (k : ℕ) _).mp le_rfl
        refine (tLeaf_le_iff he'0 h (e' * d + r) (j : ℕ) _).mpr ?_
        have hsplit : (e' * d + r) - (j : ℕ)
            = (e' * d - (i : ℕ)) + (r - (k : ℕ)) := by
          have := i.isLt
          have := k.isLt
          omega
        have hmul : h * ((e' * d - (i : ℕ)) + (r - (k : ℕ)))
            = h * (e' * d - (i : ℕ)) + h * (r - (k : ℕ)) := Nat.mul_add h _ _
        have hdist : e' * (tLeaf h e' (e' * d) (i : ℕ) + tSteep h e' r (k : ℕ))
            = e' * tLeaf h e' (e' * d) (i : ℕ) + e' * tSteep h e' r (k : ℕ) :=
          Nat.mul_add e' _ _
        rw [hsplit, hmul, hdist]
        omega
      · intro k hk
        have hB : h * (r - (k : ℕ)) < e' * tSteep h e' r (k : ℕ) :=
          (tSteep_le_iff he'0 h r (k : ℕ) _).mp le_rfl
        refine (tLeaf_le_iff he'0 h (e' * d + r) (j : ℕ) _).mpr ?_
        have hsplit : (e' * d + r) - (j : ℕ) = r - (k : ℕ) := by
          have := k.isLt
          omega
        rw [hsplit]
        omega
      · intro i hik
        have hA : h * (e' * d - (i : ℕ)) ≤ e' * tLeaf h e' (e' * d) (i : ℕ) :=
          (tLeaf_le_iff he'0 h (e' * d) (i : ℕ) _).mp le_rfl
        refine (tLeaf_le_iff he'0 h (e' * d + r) (j : ℕ) _).mpr ?_
        have hsplit : (e' * d + r) - (j : ℕ) = e' * d - (i : ℕ) := by
          have := i.isLt
          omega
        rw [hsplit]
        omega
    have hcapK : tLeaf h e' (e' * d + r) (j : ℕ) ≤ K := by
      have h1 := tLeaf_antitone h e' (e' * d + r) (Nat.zero_le (j : ℕ))
      omega
    have h1 : tLeaf h e' (e' * d + r) (j : ℕ)
        ≤ resOrd (proj O (e' * d + r) K
            (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) j) :=
      (le_classCoeffVal_iff_dvd hπ hcapK rfl j).mpr hdvd
    have h2 : h * ((e' * d + r) - (j : ℕ)) ≤ e' * tLeaf h e' (e' * d + r) (j : ℕ) :=
      (tLeaf_le_iff he'0 h (e' * d + r) (j : ℕ) _).mp le_rfl
    have h3 : e' * tLeaf h e' (e' * d + r) (j : ℕ)
        ≤ e' * resOrd (proj O (e' * d + r) K
            (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) j) :=
      Nat.mul_le_mul_left e' h1
    omega
  · -- THE EXACT COORDINATE at abscissa r
    have hrm : r < e' * d + r := by omega
    rw [resAt_lt _ hrm]
    show resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ K)
      ((monicPoly a₁ * monicPoly a₂).coeff
        ((⟨r, hrm⟩ : Fin (e' * d + r)) : ℕ))) = h * d
    -- the difference from the corner term is strictly deeper
    have hrest : π ^ (h * d + 1)
        ∣ (monicPoly a₁ * monicPoly a₂).coeff r - a₁ ⟨0, hn0⟩ := by
      rw [Polynomial.coeff_mul]
      have hmem : ((0 : ℕ), r) ∈ Finset.antidiagonal r := by
        simp
      have hsplit := Finset.sum_erase_add (Finset.antidiagonal r)
        (fun x => (monicPoly a₁).coeff x.1 * (monicPoly a₂).coeff x.2) hmem
      have hterm : (monicPoly a₁).coeff 0 * (monicPoly a₂).coeff r = a₁ ⟨0, hn0⟩ := by
        have htop : (monicPoly a₂).coeff r = 1 := by
          have h1 := (monicPoly_monic a₂).coeff_natDegree
          rwa [monicPoly_natDegree] at h1
        rw [monicPoly_coeff_lt a₁ hn0, htop, mul_one]
      have hdiff : (∑ x ∈ Finset.antidiagonal r,
            (monicPoly a₁).coeff x.1 * (monicPoly a₂).coeff x.2) - a₁ ⟨0, hn0⟩
          = ∑ x ∈ (Finset.antidiagonal r).erase (0, r),
              (monicPoly a₁).coeff x.1 * (monicPoly a₂).coeff x.2 := by
        rw [← hsplit, hterm]
        ring
      rw [hdiff]
      refine Finset.dvd_sum fun x hx => ?_
      have hxne := Finset.ne_of_mem_erase hx
      have hxmem := Finset.mem_of_mem_erase hx
      rw [Finset.mem_antidiagonal] at hxmem
      rcases Nat.lt_or_ge x.1 (e' * d) with hi | hi
      · rcases Nat.lt_or_ge x.2 r with hk | hk
        · -- interior term: i ≥ 1 forced, threshold sum = h·d + 1 exactly
          have hi1 : 1 ≤ x.1 := by
            rcases Nat.eq_zero_or_pos x.1 with h0 | h1
            · exfalso
              refine hxne ?_
              have : x.2 = r := by omega
              exact Prod.ext h0 this
            · exact h1
          rw [monicPoly_coeff_lt a₁ hi, monicPoly_coeff_lt a₂ hk]
          have h1 := mul_dvd_mul (hL2 ⟨x.1, hi⟩) (hS ⟨x.2, hk⟩)
          rw [← pow_add] at h1
          refine (pow_dvd_pow π ?_).trans h1
          show h * d + 1 ≤ tLeaf h e' (e' * d) x.1 + tSteep h e' r x.2
          -- h·d + 1 ≤ tLeaf(i) + tSteep(k) for i + k = r, i ≥ 1
          have hA : h * (e' * d - x.1) ≤ e' * tLeaf h e' (e' * d) x.1 :=
            (tLeaf_le_iff he'0 h (e' * d) x.1 _).mp le_rfl
          have hB : h * (r - x.2) < e' * tSteep h e' r x.2 :=
            (tSteep_le_iff he'0 h r x.2 _).mp le_rfl
          have hx1 : r - x.2 = x.1 := by omega
          rw [hx1] at hB
          have hjoin : h * (e' * d - x.1) + h * x.1 = e' * (h * d) := by
            rw [← Nat.mul_add]
            have h2 : e' * d - x.1 + x.1 = e' * d := by omega
            rw [h2]
            ring
          have hdist : e' * (tLeaf h e' (e' * d) x.1 + tSteep h e' r x.2)
              = e' * tLeaf h e' (e' * d) x.1 + e' * tSteep h e' r x.2 :=
            Nat.mul_add e' _ _
          have hlt : e' * (h * d) < e' * (tLeaf h e' (e' * d) x.1 + tSteep h e' r x.2) := by
            omega
          have := Nat.lt_of_mul_lt_mul_left hlt
          omega
        · rcases Nat.eq_or_lt_of_le hk with hk' | hk'
          · -- x.2 = r forces x.1 = 0: excluded by the erase
            exfalso
            refine hxne ?_
            have h0 : x.1 = 0 := by omega
            exact Prod.ext h0 hk'.symm
          · have hz : (monicPoly a₂).coeff x.2 = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt
                (by rw [monicPoly_natDegree]; exact hk')
            rw [hz, mul_zero]
            exact dvd_zero _
      · rcases Nat.eq_or_lt_of_le hi with hi' | hi'
        · -- x.1 = e'd: the block top against a deep steep coefficient
          rcases Nat.lt_or_ge x.2 r with hk | hk
          · have htop : (monicPoly a₁).coeff x.1 = 1 := by
              rw [← hi']
              have h1 := (monicPoly_monic a₁).coeff_natDegree
              rwa [monicPoly_natDegree] at h1
            rw [htop, one_mul, monicPoly_coeff_lt a₂ hk]
            refine (pow_dvd_pow π ?_).trans (hS ⟨x.2, hk⟩)
            show h * d + 1 ≤ tSteep h e' r x.2
            -- h·d + 1 ≤ tSteep(x.2) with r − x.2 = e'·d
            have hB : h * (r - x.2) < e' * tSteep h e' r x.2 :=
              (tSteep_le_iff he'0 h r x.2 _).mp le_rfl
            have hx2 : r - x.2 = e' * d := by omega
            rw [hx2] at hB
            have h2 : h * (e' * d) = e' * (h * d) := by ring
            rw [h2] at hB
            have := Nat.lt_of_mul_lt_mul_left hB
            omega
          · omega
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
              (by rw [monicPoly_natDegree]; exact hi'), zero_mul]
          exact dvd_zero _
    have hPdvd : π ^ (h * d) ∣ (monicPoly a₁ * monicPoly a₂).coeff r := by
      have h1 : (monicPoly a₁ * monicPoly a₂).coeff r
          = a₁ ⟨0, hn0⟩ + ((monicPoly a₁ * monicPoly a₂).coeff r - a₁ ⟨0, hn0⟩) := by
        ring
      rw [h1]
      exact dvd_add hc0dvd ((pow_dvd_pow π (by omega)).trans hrest)
    have hPndvd : ¬ π ^ (h * d + 1) ∣ (monicPoly a₁ * monicPoly a₂).coeff r := by
      intro hcon
      refine hc0ndvd ?_
      have h1 : a₁ ⟨0, hn0⟩ = (monicPoly a₁ * monicPoly a₂).coeff r
          - ((monicPoly a₁ * monicPoly a₂).coeff r - a₁ ⟨0, hn0⟩) := by
        ring
      rw [h1]
      exact dvd_sub hcon hrest
    exact resOrd_mk_eq hπ (by omega) hPdvd (Or.inr hPndvd)
  · -- THE STRICTLY-RAISED CORNER at abscissa 0
    have h0m : (0 : ℕ) < e' * d + r := by omega
    rw [resAt_lt _ h0m]
    have hdvd : π ^ (h * d + tSteep h e' r 0)
        ∣ (monicPoly a₁ * monicPoly a₂).coeff 0 := by
      refine prod_coeff_dvd hL2 hS _ 0 (by omega) ?_ ?_ ?_
      · intro i k hik
        have hi0 : (i : ℕ) = 0 := by omega
        have hk0 : (k : ℕ) = 0 := by omega
        rw [hi0, hk0]
        have h1 := hd_le_tLeaf_zero (d := d) hh hhe
        omega
      · intro k hk
        exfalso
        omega
      · intro i hik
        exfalso
        have := i.isLt
        omega
    have h1 : h * d + tSteep h e' r 0
        ≤ resOrd (proj O (e' * d + r) K
            (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) ⟨0, h0m⟩) :=
      (le_classCoeffVal_iff_dvd hπ hK rfl ⟨0, h0m⟩).mpr hdvd
    have h2 : e' * (h * d + tSteep h e' r 0)
        = e' * (h * d) + e' * tSteep h e' r 0 := Nat.mul_add e' _ _
    have h3 : e' * (h * d + tSteep h e' r 0)
        ≤ e' * resOrd (proj O (e' * d + r) K
            (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) ⟨0, h0m⟩) :=
      Nat.mul_le_mul_left e' h1
    omega

end ProductData

/-! ## §5 — THE FACE PACKAGE at general r: minimal face `(h, e')` not attained at `0`,
stratum, shallow, and non-pure-face, at mass `m = e'·d + r` -/

section FacePackage

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The face package at general r**: a mass-`(e'd + r)` class carrying the frame
cone with the exact abscissa-`r` coordinate and the strictly-raised corner has minimal
face `(h, e')` NOT attained at `0`, lies in the `X^m`-stratum and the shallow set, and
avoids every integer-slope pure-face box. -/
private theorem face_package_gen {h e' d r : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d) (hr : 0 < r)
    {K : ℕ} (hmK : e' * d + r ≤ K) {c : Coeff O (e' * d + r) K}
    (hcone : ∀ j : Fin (e' * d + r),
      h * ((e' * d + r) - (j : ℕ)) ≤ e' * resOrd (c j))
    (hone : resOrd (resAt c r) = h * d)
    (hzero : e' * (h * d) + h * r < e' * resOrd (resAt c 0)) :
    MinFaceAt c h e' ∧ ¬ NPAttains c h e' 0
      ∧ c ∈ levelZeroStratum O (e' * d + r) K (Polynomial.X ^ (e' * d + r))
      ∧ c ∈ shallowSet O (e' * d + r) K
      ∧ c ∉ pureFaceSet O (e' * d + r) K := by
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have h0m : (0 : ℕ) < e' * d + r := by omega
  have hrm : r < e' * d + r := by omega
  have hre0 : resAt c 0 = c ⟨0, h0m⟩ := resAt_lt c h0m
  have hrer : resAt c r = c ⟨r, hrm⟩ := resAt_lt c hrm
  rw [hre0] at hzero
  rw [hrer] at hone
  have hnp0 : npHeight c 0 = resOrd (c ⟨0, h0m⟩) := by
    have h5 := npHeight_coe c ⟨0, h0m⟩
    simpa using h5
  have hnpr : npHeight c r = resOrd (c ⟨r, hrm⟩) := by
    have h5 := npHeight_coe c ⟨r, hrm⟩
    simpa using h5
  have hnpm : npHeight c (e' * d + r) = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl (e' * d + r))]
  have hkey : e' * (h * d) + h * r = h * (e' * d + r) := by ring
  -- the support is h·m, attained at r and m, missed at 0
  have hsup : classNPSupport c h e' = h * (e' * d + r) := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h2 := classNPSupport_le_apply c h e' (by omega : r ≤ e' * d + r)
      rw [hnpr, hone] at h2
      omega
    · intro i hi
      rcases eq_or_lt_of_le hi with heq | hilt
      · subst heq
        rw [hnpm]
        omega
      · have hf : h * ((e' * d + r) - i) ≤ e' * resOrd (c ⟨i, hilt⟩) := by
          simpa using hcone ⟨i, hilt⟩
        have hnp : npHeight c i = resOrd (c ⟨i, hilt⟩) := by
          have h5 := npHeight_coe c ⟨i, hilt⟩
          simpa using h5
        rw [hnp]
        have hdist : h * ((e' * d + r) - i) + h * i = h * (e' * d + r) := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hilt)]
        omega
  have hAr : NPAttains c h e' r := by
    refine ⟨by omega, ?_⟩
    rw [hnpr, hone, hsup]
    ring
  have hAm : NPAttains c h e' (e' * d + r) := by
    refine ⟨le_refl _, ?_⟩
    rw [hnpm, hsup]
    ring
  have hnA0 : ¬ NPAttains c h e' 0 := by
    rintro ⟨-, h2⟩
    rw [hnp0, hsup, Nat.mul_zero, Nat.add_zero] at h2
    omega
  have hvis : NPVisibleAt c h e' := by
    show classNPSupport c h e' < e' * K
    rw [hsup]
    have h1 : h * (e' * d + r) < e' * (e' * d + r) := by
      have := (Nat.mul_lt_mul_right (show 0 < e' * d + r by omega)).mpr hhe
      omega
    have h2 : e' * (e' * d + r) ≤ e' * K := Nat.mul_le_mul_left e' hmK
    omega
  have hF : MinFaceAt c h e' :=
    ⟨hh1, hhe, hcop, ⟨r, e' * d + r, by omega, hAr, hAm⟩, hAm, hvis⟩
  have hstr : c ∈ levelZeroStratum O (e' * d + r) K (Polynomial.X ^ (e' * d + r)) := by
    refine (mem_stratum_X_pow_iff (by omega : 1 ≤ K) c).2 fun i => ?_
    have h1 := hcone i
    have h2 : 0 < h * ((e' * d + r) - (i : ℕ)) :=
      Nat.mul_pos (by omega) (by have := i.isLt; omega)
    rcases Nat.eq_zero_or_pos (resOrd (c i)) with h3 | h3
    · rw [h3, Nat.mul_zero] at h1
      omega
    · exact h3
  have hsh : c ∈ shallowSet O (e' * d + r) K := by
    refine ⟨⟨r, hrm⟩, ?_⟩
    show resOrd (c ⟨r, hrm⟩) < (e' * d + r) - r
    rw [hone]
    have h1 : h * d < e' * d := by
      have := (Nat.mul_lt_mul_right hd0).mpr hhe
      omega
    omega
  have hnpure : c ∉ pureFaceSet O (e' * d + r) K := by
    rintro ⟨h'', hmem'', hb1, hb2⟩
    have hat_r := hb2 ⟨r, hrm⟩
    have hnpr' : npHeight c ((⟨r, hrm⟩ : Fin (e' * d + r)) : ℕ) = h * d := by
      rw [show ((⟨r, hrm⟩ : Fin (e' * d + r)) : ℕ) = r from rfl, hnpr, hone]
    rw [hnpr'] at hat_r
    have hsub : (e' * d + r) - ((⟨r, hrm⟩ : Fin (e' * d + r)) : ℕ) = e' * d := by
      show (e' * d + r) - r = e' * d
      omega
    rw [hsub] at hat_r
    have hb1' : h'' = resOrd (c ⟨0, h0m⟩) := by rw [← hnp0, hb1]
    have hstrict : e' * (h * d) + h * r < e' * h'' := by
      rw [hb1']
      exact hzero
    have hmul1 : e' * (h'' * (e' * d)) ≤ e' * ((e' * d + r) * (h * d)) :=
      Nat.mul_le_mul_left e' hat_r
    have hmul2 : (e' * (h * d) + h * r) * (e' * d) < (e' * h'') * (e' * d) :=
      (Nat.mul_lt_mul_right hn0).mpr hstrict
    have e1 : (e' * h'') * (e' * d) = e' * (h'' * (e' * d)) := by ring
    have e2 : (e' * (h * d) + h * r) * (e' * d)
        = e' * (h * d) * (e' * d) + h * r * (e' * d) := by ring
    have e3 : e' * ((e' * d + r) * (h * d))
        = e' * (h * d) * (e' * d) + h * r * (e' * d) := by ring
    omega
  exact ⟨hF, hnA0, hstr, hsh, hnpure⟩

end FacePackage

/-! ## §6 — THE PRODUCT RESIDUAL at general r: `classResidualPoly (γ·ρ) =
classResidualPoly γ · unit` — the strict cone collapses the steep side to its monic
point, so its side residual is a nonzero constant -/

section ProductResidual

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- `classSideSet` membership through the Classical filter (IFCG57's private
replica). -/
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

/-- The monic top point has height `0` (IFCG66's private replica). -/
private theorem npHgt_monic_top {g : Polynomial O} (hg : g.Monic) :
    npHgt X g g.natDegree = 0 := by
  rw [npHgt_X, hg.coeff_natDegree]
  exact IsDiscreteValuationRing.addVal_one

/-- A monic polynomial's cleared support value is finite (IFCG66's private
replica). -/
private theorem suppVal_ne_top_of_monic {g : Polynomial O} (hg : g.Monic) (u ℓ : ℕ) :
    suppVal X g u ℓ ≠ ⊤ := by
  have hle : suppVal X g u ℓ ≤ ℓ • npHgt X g g.natDegree + ((u * g.natDegree : ℕ) : ℕ∞) := by
    rw [suppVal]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  rw [npHgt_monic_top hg, smul_zero, zero_add] at hle
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle

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

/-- **The steep class side data**: the strict cone forces the `(h, e')`-side of a
mass-`r` class to its monic point — support `h·r`, attained ONLY at `r`. -/
private theorem steep_class_side {h e' r : ℕ}
    (hh : 0 < h) (hhe : h < e') (hr : 0 < r) {K : ℕ} (hrK : r ≤ K)
    {a₂ : Fin r → O} (hsteep : proj O r K a₂ ∈ steepCone O r K h e') :
    classNPSupport (proj O r K a₂) h e' = h * r
      ∧ classSideSet (proj O r K a₂) h e' = {r}
      ∧ NPVisibleAt (proj O r K a₂) h e' := by
  have he'0 : 0 < e' := by omega
  have hnpρtop : npHeight (proj O r K a₂) r = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl r)]
  have hsupρ : classNPSupport (proj O r K a₂) h e' = h * r := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h2 := classNPSupport_le_apply (proj O r K a₂) h e' (le_refl r)
      rw [hnpρtop] at h2
      omega
    · intro i hi
      rcases eq_or_lt_of_le hi with heq | hilt
      · subst heq
        rw [hnpρtop]
        omega
      · have hf : h * (r - i) < e' * resOrd (proj O r K a₂ ⟨i, hilt⟩) := by
          simpa using hsteep ⟨i, hilt⟩
        have hnp : npHeight (proj O r K a₂) i
            = resOrd (proj O r K a₂ ⟨i, hilt⟩) := by
          have h5 := npHeight_coe (proj O r K a₂) ⟨i, hilt⟩
          simpa using h5
        rw [hnp]
        have hdist : h * (r - i) + h * i = h * r := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hilt)]
        omega
  have hArρ : NPAttains (proj O r K a₂) h e' r := by
    refine ⟨le_refl r, ?_⟩
    rw [hnpρtop, hsupρ]
    ring
  have hnAρ : ∀ i, i < r → ¬ NPAttains (proj O r K a₂) h e' i := by
    intro i hilt
    rintro ⟨-, hc⟩
    have hnp : npHeight (proj O r K a₂) i = resOrd (proj O r K a₂ ⟨i, hilt⟩) := by
      have h5 := npHeight_coe (proj O r K a₂) ⟨i, hilt⟩
      simpa using h5
    rw [hnp, hsupρ] at hc
    have hf : h * (r - i) < e' * resOrd (proj O r K a₂ ⟨i, hilt⟩) := by
      simpa using hsteep ⟨i, hilt⟩
    have hdist : h * (r - i) + h * i = h * r := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hilt)]
    omega
  have hvisρ : NPVisibleAt (proj O r K a₂) h e' := by
    show classNPSupport (proj O r K a₂) h e' < e' * K
    rw [hsupρ]
    have h1 : h * r < e' * r := by
      have := (Nat.mul_lt_mul_right hr).mpr hhe
      omega
    have h2 : e' * r ≤ e' * K := Nat.mul_le_mul_left e' hrK
    omega
  refine ⟨hsupρ, ?_, hvisρ⟩
  ext j
  rw [mem_classSideSet_iff', Finset.mem_singleton]
  constructor
  · rintro ⟨hj2, hAt⟩
    by_contra hne
    have hjlt : j < r := by omega
    exact hnAρ j hjlt hAt
  · rintro rfl
    exact ⟨by omega, hArρ⟩

/-- **The residual factorization at general r**: the canonical residual of the product
class is the block's residual times a UNIT, with both degrees pinned to `d`. -/
private theorem prod_residual_gen {π : O} (hπ : Irreducible π) {h e' d r : ℕ}
    (hh : 0 < h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d) (hr : 0 < r)
    {K : ℕ} (hmK : e' * d + r ≤ K) (hK : h * d + tSteep h e' r 0 ≤ K)
    {a₁ : Fin (e' * d) → O} {a₂ : Fin r → O}
    (hcone : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) K a₁ j))
    (hcorner : resOrd (resAt (proj O (e' * d) K a₁) 0) = h * d)
    (hsteep : proj O r K a₂ ∈ steepCone O r K h e') :
    ∃ u : Polynomial (resField (X : Polynomial O)), IsUnit u
      ∧ classResidualPoly π (proj O (e' * d + r) K
          (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e'
        = classResidualPoly π (proj O (e' * d) K a₁) h e' * u
      ∧ (classResidualPoly π (proj O (e' * d) K a₁) h e').natDegree = d
      ∧ (classResidualPoly π (proj O (e' * d + r) K
          (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e').natDegree = d := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hrK : r ≤ K := by omega
  -- the block's class face data at its own mass
  have hcorner' : resOrd (proj O (e' * d) K a₁ ⟨0, hn0⟩) = h * d := by
    rw [← resAt_lt (proj O (e' * d) K a₁) hn0]
    exact hcorner
  obtain ⟨hsupγ, hA0γ, hAmγ, hvisγ⟩ :=
    leafCone_face_data hh hhe hd0 rfl hn0 (by omega : e' * d ≤ K) hcone hcorner'
  -- the steep factor's class side data at mass r
  obtain ⟨hsupρ, hclassρ, hvisρ⟩ := steep_class_side hh hhe hr hrK hsteep
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
    have hts1 : 0 < tSteep h e' r 0 := Nat.succ_le_succ (Nat.zero_le _)
    omega
  have hHg' : npHgt X (monicPoly a₁) (sideMin X (monicPoly a₁) h e' hnf)
      = ((h * d : ℕ) : ℕ∞) := by
    rw [hming]
    have h1 := npHgt_monicPoly_eq hπ
      (rfl : proj O (e' * d) K a₁ = proj O (e' * d) K a₁) hn0 hvis0γ
    rw [h1, show classCoeffVal (proj O (e' * d) K a₁) ⟨0, hn0⟩ = h * d from hcorner']
  -- the steep factor's lift-side side data
  have hnz : (sideSet X (monicPoly a₂) h e').Nonempty := sideSet_nonempty_gen _ _ _ _
  have hsetR : sideSet X (monicPoly a₂) h e' = {r} := by
    rw [sideSet_monicPoly_eq hπ he'0 hvisρ rfl]
    exact hclassρ
  have hminR : sideMin X (monicPoly a₂) h e' hnz = r := by
    refine le_antisymm
      (Finset.min'_le _ r (by rw [hsetR]; exact Finset.mem_singleton_self r)) ?_
    refine Finset.le_min' _ _ _ fun y hy => ?_
    rw [hsetR, Finset.mem_singleton] at hy
    omega
  have hmaxR : sideMax X (monicPoly a₂) h e' hnz = r := by
    refine le_antisymm ?_
      (Finset.le_max' _ r (by rw [hsetR]; exact Finset.mem_singleton_self r))
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
  have hPdeg : (monicPoly a₁ * monicPoly a₂).natDegree = e' * d + r := by
    rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic a₂),
      monicPoly_natDegree, monicPoly_natDegree]
  have hmp : monicPoly (fun i : Fin (e' * d + r) =>
      (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)) = monicPoly a₁ * monicPoly a₂ :=
    monicPoly_coeff_eq_self hPm hPdeg
  -- the product class's visibility (through the general face package)
  obtain ⟨hconeP, honeP, hzeroP⟩ :=
    prod_class_data_gen hπ hh hhe hd0 hr hK hcone hcorner hsteep
  obtain ⟨hFP, -, -, -, -⟩ :=
    face_package_gen (by omega) hhe hcop hd0 hr hmK hconeP honeP hzeroP
  have hvisP : NPVisibleAt (proj O (e' * d + r) K
      (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e' := hFP.2.2.2.2.2
  -- the H-data on the product frame
  have hne_c : (sideSet X (monicPoly (fun i : Fin (e' * d + r) =>
      (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e').Nonempty :=
    sideSet_nonempty_gen _ _ _ _
  have hnp0r : npHgt X (monicPoly a₁ * monicPoly a₂) (0 + r)
      = ((h * d + 0 : ℕ) : ℕ∞) := by
    have h2 := hnpmul
    rw [hming, hminR] at h2
    exact h2
  have hH_c : npHgt X (monicPoly (fun i : Fin (e' * d + r) =>
      (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ)))
      (sideMin X (monicPoly (fun i : Fin (e' * d + r) =>
        (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e' hne_c)
      = ((h * d + 0 : ℕ) : ℕ∞) := by
    have h1 : sideMin X (monicPoly (fun i : Fin (e' * d + r) =>
        (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e' hne_c = 0 + r := by
      rw [sideMin_congr hmp hne_c hnfz, hminmul, hming, hminR]
    rw [h1, hmp]
    exact hnp0r
  -- the product's residual factors
  have hcrpP : classResidualPoly π (proj O (e' * d + r) K
      (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e'
      = resPoly π X (monicPoly (fun i : Fin (e' * d + r) =>
          (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e' hne_c (h * d + 0) :=
    classResidualPoly_eq hπ he'0 hvisP rfl hne_c hH_c
  have hrescP : classResidualPoly π (proj O (e' * d + r) K
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

/-! ## §7 — THE DECIDEDNESS LEG AND THE IMAGE: (pinned box) × (steep, decided at the
shifted window) lands in `subfaceCell` at mass `e'·d + r` -/

section Image

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The box decision at an arbitrary shifted window** (SFW's engine, shift
generalized from `h·d` to any `v ≥ h·d`): every pinned-box read lives at digit levels
≤ `h·d`, so the data truncates from window `K` to `K − v` and IFCG37's spanning
decision fires there. -/
private theorem box_decided_shifted_gen {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d)
    {v K : ℕ} (hv : h * d ≤ v) (hK2 : v + h * d < K) (hKm : e' * d + v ≤ K)
    {a₁ : Fin (e' * d) → O}
    (hcone : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) K a₁ j))
    (hcorner : resOrd (resAt (proj O (e' * d) K a₁) 0) = h * d)
    (hirr : Irreducible (leafResPoly π h e' d (proj O (e' * d) K a₁))) :
    DecidedAt O (e' * d) ⟨{(e', d)}⟩ (K - v) (proj O (e' * d) (K - v) a₁) := by
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hdK' : h * d < K - v := by omega
  have hnK' : e' * d ≤ K - v := by omega
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
  have hcone' : ∀ j : Fin (e' * d),
      h * (e' * d - (j : ℕ)) ≤ e' * resOrd (proj O (e' * d) (K - v) a₁ j) := by
    intro j
    have hcap : tLeaf h e' (e' * d) (j : ℕ) ≤ h * d := tLeaf_le_corner he'0 h d _
    have h1 : tLeaf h e' (e' * d) (j : ℕ)
        ≤ resOrd (proj O (e' * d) (K - v) a₁ j) :=
      (le_classCoeffVal_iff_dvd hπ (by omega) rfl j).mpr (hL2 j)
    have h2 : h * (e' * d - (j : ℕ)) ≤ e' * tLeaf h e' (e' * d) (j : ℕ) :=
      (tLeaf_le_iff he'0 h (e' * d) (j : ℕ) _).mp le_rfl
    have h3 : e' * tLeaf h e' (e' * d) (j : ℕ)
        ≤ e' * resOrd (proj O (e' * d) (K - v) a₁ j) :=
      Nat.mul_le_mul_left e' h1
    omega
  have hcorner'' : resOrd (proj O (e' * d) (K - v) a₁ ⟨0, hn0⟩) = h * d := by
    show resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ (K - v)) (a₁ ⟨0, hn0⟩)) = h * d
    exact resOrd_mk_eq hπ (by omega) hL1.1 (Or.inr hL1.2)
  have hdig : leafResPoly π h e' d (proj O (e' * d) (K - v) a₁)
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
        (Ideal.Quotient.mk ((maximalIdeal O) ^ (K - v)) (a₁ ⟨e' * k, hek⟩))
      = resDig π (h * (d - k))
        (Ideal.Quotient.mk ((maximalIdeal O) ^ K) (a₁ ⟨e' * k, hek⟩))
    rw [resDig_mk hπ (by omega), resDig_mk hπ (by omega)]
  obtain ⟨-, hA0', hAm', hvis'⟩ :=
    leafCone_face_data hh hhe hd0 rfl hn0 hnK' hcone' hcorner''
  have hstr' : proj O (e' * d) (K - v) a₁
      ∈ levelZeroStratum O (e' * d) (K - v) (Polynomial.X ^ (e' * d)) := by
    refine (mem_stratum_X_pow_iff (by omega : 1 ≤ K - v) _).2 fun i => ?_
    have h1 := hcone' i
    have h2 : 0 < h * (e' * d - (i : ℕ)) :=
      Nat.mul_pos (by omega) (by have := i.isLt; omega)
    rcases Nat.eq_zero_or_pos (resOrd (proj O (e' * d) (K - v) a₁ i)) with h3 | h3
    · rw [h3, Nat.mul_zero] at h1
      omega
    · exact h3
  have hirrC' : Irreducible (classResidualPoly π (proj O (e' * d) (K - v) a₁) h e') := by
    refine (irreducible_classResidualPoly_iff hπ hh hhe hd0 rfl hn0 hnK'
      hcone' hcorner'').mpr ?_
    rw [hdig]
    exact hirr
  exact decidedAt_of_spanning_irr hd0 hπ hn0 hh he'0 hcop rfl hstr' hA0' hAm' hvis' hirrC'

/-- ★★ **THE IMAGE at general r**: the `mulClass` of a pinned-box class and a steep
class DECIDED-`τ` at the `h·d·r`-shifted window IS a sub-face leaf cell at the frame
`(h, e', d)` and the type `σ = (e',d) ::ₘ τ` — decided (the box leg discharged by the
shifted spanning decision, the steep leg by hypothesis), stratified, shallow,
non-pure-face, with minimal face `(h, e')` not attained at `0` and irreducible
degree-`d` residual. -/
theorem mul_mem_subfaceCell_gen {π : O} (hπ : Irreducible π) {h e' d r : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d) (hr : 0 < r)
    {σ τ : FactorizationType} (hσ : σ.data = (e', d) ::ₘ τ.data) {M : ℕ}
    (hM : 2 * (h * d * r) ≤ M)
    {a₁ : Fin (e' * d) → O} {a₂ : Fin r → O}
    (hγ : proj O (e' * d) (M + (e' * d + r)) a₁
      ∈ pinnedBox π (M + (e' * d + r)) h e' d)
    (hρ : proj O r (M + (e' * d + r)) a₂ ∈ steepCone O r (M + (e' * d + r)) h e')
    (hdec₂ : DecidedAt O r τ (M + (e' * d + r) - h * d * r)
      (proj O r (M + (e' * d + r) - h * d * r) a₂)) :
    mulClass (proj O (e' * d) (M + (e' * d + r)) a₁)
        (proj O r (M + (e' * d + r)) a₂)
      ∈ subfaceCell O π (e' * d + r) h e' d σ M := by
  have hh : 0 < h := hh1
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hhd1 : 1 ≤ h * d := Nat.mul_pos hh hd0
  have hhdv : h * d ≤ h * d * r := Nat.le_mul_of_pos_right _ hr
  have hrv : r ≤ h * d * r := by
    have h2 : 1 * r ≤ (h * d) * r := Nat.mul_le_mul_right r hhd1
    omega
  set K := M + (e' * d + r) with hKdef
  have htsr : tSteep h e' r 0 ≤ r := tSteep_le_mass hh hhe r 0 hr
  have hK : h * d + tSteep h e' r 0 ≤ K := by omega
  have hmK : e' * d + r ≤ K := by omega
  obtain ⟨hcone, hcorner, hirr⟩ := hγ
  have hsteep' : ∀ j : Fin r,
      h * (r - (j : ℕ)) < e' * resOrd (proj O r K a₂ j) := fun j => hρ j
  -- the coefficient facts and the face package
  obtain ⟨hconeP, honeP, hzeroP⟩ :=
    prod_class_data_gen hπ hh hhe hd0 hr hK hcone hcorner hρ
  obtain ⟨hF, hnA0, hstr, hsh, hnpure⟩ :=
    face_package_gen hh1 hhe hcop hd0 hr hmK hconeP honeP hzeroP
  -- the residual: irreducible of degree d
  obtain ⟨u, huu, hfac, -, hdegP⟩ :=
    prod_residual_gen hπ hh hhe hcop hd0 hr hmK hK hcone hcorner hρ
  have hcorner' : resOrd (proj O (e' * d) K a₁ ⟨0, hn0⟩) = h * d := by
    rw [← resAt_lt (proj O (e' * d) K a₁) hn0]
    exact hcorner
  have hirrA : Irreducible
      (classResidualPoly π (proj O (e' * d) K a₁) h e') :=
    (irreducible_classResidualPoly_iff hπ hh hhe hd0 rfl hn0 (by omega)
      hcone hcorner').mpr hirr
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hirrC : Irreducible (classResidualPoly π (proj O (e' * d + r) K
      (fun i => (monicPoly a₁ * monicPoly a₂).coeff (i : ℕ))) h e') := by
    rw [hfac]
    have hassoc : Associated
        (classResidualPoly π (proj O (e' * d) K a₁) h e')
        (classResidualPoly π (proj O (e' * d) K a₁) h e' * u) :=
      ⟨huu.unit, by rw [IsUnit.unit_spec]⟩
    exact hassoc.irreducible hirrA
  -- the decidedness: DPN's coupling, box leg discharged, steep leg by hypothesis
  have hdec₁ := box_decided_shifted_gen hπ hh hhe hcop hd0 hhdv
    (by omega : h * d * r + h * d < K) (by omega : e' * d + h * d * r ≤ K)
    hcone hcorner hirr
  have hdec := decidedAt_mulClass_of_cones hπ he'0 hd0 hr
    (by omega : 2 * (h * d * r) + 1 ≤ K) hcone hcorner' hsteep' hdec₁ hdec₂
  have hdata : (FactorizationType.mk {(e', d)}).data + τ.data = σ.data := by
    show ({(e', d)} : Multiset (ℕ × ℕ)) + τ.data = σ.data
    rw [hσ, Multiset.singleton_add]
  rw [hdata] at hdec
  have hσeta : (⟨σ.data⟩ : FactorizationType) = σ := rfl
  rw [hσeta] at hdec
  -- assembly through `mulClass_proj`
  rw [← mulClass_proj a₁ a₂] at hdec ⊢
  exact ⟨⟨⟨⟨⟨hdec, hstr⟩, hsh⟩, hnpure⟩, h, e', hF, hirrC, hnA0⟩, hF, hdegP⟩

end Image

/-! ## §8 — THE SURJECTION at general r AND THE DRAINAGE DISSOLUTION: every sub-face
cell factors through (pinned box) × (steep cone), the type is forced, and — the key
new observation — the steep factor class is decided at the FULL window, pointwise, by
`typeOf_mul` + the box's forced type + multiset cons-cancellation.  LSF's fence 2
(shifted-level factor decidedness) is nowhere needed. -/

section Surjectivity

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **THE FACTORIZATION OF THE CELL at general r** (LSF's transport pushed into
the carriers): every sub-face cell at frame `(h, e', d)` with cofactor mass
`r = m − e'·d` is `mulClass γ ρ` for a pinned-box class `γ` and a steep-cone class
`ρ`; the ambient type is forced to `(e',d) ::ₘ typeOf(cofactor)`; and the steep
factor is DECIDED at its type at the FULL window. -/
theorem subfaceCell_factors_gen {π : O} (hπ : Irreducible π) {h e' d r : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d) (hr : 0 < r)
    {σ : FactorizationType} {M : ℕ}
    {c : Coeff O (e' * d + r) (M + (e' * d + r))}
    (hc : c ∈ subfaceCell O π (e' * d + r) h e' d σ M) :
    ∃ (a₁ : Fin (e' * d) → O) (a₂ : Fin r → O),
      proj O (e' * d) (M + (e' * d + r)) a₁ ∈ pinnedBox π (M + (e' * d + r)) h e' d
      ∧ proj O r (M + (e' * d + r)) a₂ ∈ steepCone O r (M + (e' * d + r)) h e'
      ∧ mulClass (proj O (e' * d) (M + (e' * d + r)) a₁)
          (proj O r (M + (e' * d + r)) a₂) = c
      ∧ σ.data = (e', d) ::ₘ (typeOf (monicPoly a₂)).data
      ∧ DecidedAt O r (typeOf (monicPoly a₂)) (M + (e' * d + r))
          (proj O r (M + (e' * d + r)) a₂) := by
  have hh : 0 < h := hh1
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hm0 : 0 < e' * d + r := by omega
  have hhd : h * d < e' * d := by
    have := (Nat.mul_lt_mul_right hd0).mpr hhe
    omega
  obtain ⟨hsub, hF, hdeg⟩ := hc
  have hdecC : DecidedAt O (e' * d + r) σ (M + (e' * d + r)) c := hsub.1.1.1.1
  obtain ⟨a, ha⟩ := proj_surjective O (e' * d + r) (M + (e' * d + r)) c
  obtain ⟨g, R, d', heq, hgm, hRm, hgpure, hd'0, hgd, hd'm, htyg, hRdeg, hdata,
    hcrpd, hside⟩ := subface_transport_pinned hπ hm0 hsub hF ha
  -- the transported degree is the frame degree
  have hd' : d' = d := by
    rw [hcrpd] at hdeg
    exact hdeg
  rw [hd'] at hd'0 hgd hd'm htyg hRdeg hdata
  have hRr : R.natDegree = r := by omega
  -- the two carrier lift vectors
  have hmpg : monicPoly (fun i : Fin (e' * d) => g.coeff (i : ℕ)) = g :=
    monicPoly_coeff_eq_self hgm hgd
  have hmpR : monicPoly (fun i : Fin r => R.coeff (i : ℕ)) = R := by
    refine monicPoly_coeff_eq_self hRm hRr
  -- the steep cone on the cofactor class (LSF's seed through the windowed read)
  have hsteepρ : proj O r (M + (e' * d + r)) (fun i : Fin r => R.coeff (i : ℕ))
      ∈ steepCone O r (M + (e' * d + r)) h e' := by
    intro j
    have hj' : (j : ℕ) < R.natDegree := by omega
    have h1 := class_strict_cone_of_side_singleton hπ hRm hhe hside
      (by omega : R.natDegree ≤ M + (e' * d + r)) ⟨(j : ℕ), hj'⟩
    have h3 : h * (R.natDegree - (j : ℕ))
        < e' * resOrd (proj O r (M + (e' * d + r)) (fun i : Fin r => R.coeff (i : ℕ)) j) := h1
    rw [hRr] at h3
    exact h3
  -- the cone and exact corner on the block (from purity)
  obtain ⟨hpure, hcornerP⟩ := cone_data_of_isPure hπ hgm he'0 hd0 hgpure hgd
    (show h * d < (M + (e' * d + r)) by omega)
  have hcornerAt : resOrd (resAt (proj O (e' * d) (M + (e' * d + r))
      (fun i => g.coeff (i : ℕ))) 0) = h * d := by
    rw [resAt_lt _ hn0]
    exact hcornerP
  -- the product class IS c
  have hprodeq : monicPoly (fun i : Fin (e' * d) => g.coeff (i : ℕ))
      * monicPoly (fun i : Fin r => R.coeff (i : ℕ)) = monicPoly a := by
    rw [hmpg, hmpR, ← heq]
  have hveceq : (fun i : Fin (e' * d + r) =>
      (monicPoly (fun i : Fin (e' * d) => g.coeff (i : ℕ))
        * monicPoly (fun i : Fin r => R.coeff (i : ℕ))).coeff (i : ℕ)) = a := by
    funext i
    rw [hprodeq]
    exact monicPoly_coeff_lt a i.isLt
  have hmul : mulClass (proj O (e' * d) (M + (e' * d + r)) (fun i => g.coeff (i : ℕ)))
      (proj O r (M + (e' * d + r)) (fun i => R.coeff (i : ℕ))) = c := by
    rw [← mulClass_proj, hveceq, ha]
  -- the residual factorization pulls the cell's irreducibility back to the block
  have hmK : e' * d + r ≤ (M + (e' * d + r)) := by omega
  have hKres : h * d + tSteep h e' r 0 ≤ (M + (e' * d + r)) := by
    have h1 := tSteep_le_mass hh hhe r 0 hr
    omega
  obtain ⟨u, huu, hfac, -, -⟩ := prod_residual_gen hπ hh hhe hcop hd0 hr
    hmK hKres hpure hcornerAt hsteepρ
  rw [hveceq, ha] at hfac
  have hirrc : Irreducible (classResidualPoly π c h e') := by
    obtain ⟨-, h₃, e₃, hF₃, hirr₃, -⟩ := hsub
    obtain ⟨hh3, he3⟩ := minFaceAt_unique hF hF₃
    rw [← hh3, ← he3] at hirr₃
    exact hirr₃
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hirrγ : Irreducible (classResidualPoly π
      (proj O (e' * d) (M + (e' * d + r)) (fun i => g.coeff (i : ℕ))) h e') := by
    have hassoc : Associated
        (classResidualPoly π (proj O (e' * d) (M + (e' * d + r))
          (fun i => g.coeff (i : ℕ))) h e')
        (classResidualPoly π c h e') := by
      rw [hfac]
      exact ⟨huu.unit, by rw [IsUnit.unit_spec]⟩
    exact hassoc.symm.irreducible hirrc
  have hirrleaf : Irreducible (leafResPoly π h e' d
      (proj O (e' * d) (M + (e' * d + r)) (fun i => g.coeff (i : ℕ)))) :=
    (irreducible_classResidualPoly_iff hπ hh hhe hd0 rfl hn0 (by omega)
      hpure hcornerP).mp hirrγ
  -- THE DRAINAGE DISSOLUTION: the steep factor is decided at the FULL window
  have hdecρ : DecidedAt O r (typeOf R) (M + (e' * d + r))
      (proj O r (M + (e' * d + r)) (fun i : Fin r => R.coeff (i : ℕ))) := by
    intro s hs
    have hprodproj : proj O (e' * d + r) (M + (e' * d + r))
        (fun i => (monicPoly (fun i : Fin (e' * d) => g.coeff (i : ℕ))
          * monicPoly s).coeff (i : ℕ)) = c := by
      rw [mulClass_proj, hs]
      exact hmul
    have htypeprod := hdecC _ hprodproj
    have hmpF : monicPoly (fun i : Fin (e' * d + r) =>
        (monicPoly (fun i : Fin (e' * d) => g.coeff (i : ℕ))
          * monicPoly s).coeff (i : ℕ))
        = monicPoly (fun i : Fin (e' * d) => g.coeff (i : ℕ)) * monicPoly s := by
      refine monicPoly_coeff_eq_self
        ((monicPoly_monic _).mul (monicPoly_monic s)) ?_
      rw [(monicPoly_monic _).natDegree_mul (monicPoly_monic s),
        monicPoly_natDegree, monicPoly_natDegree]
    rw [hmpF, hmpg] at htypeprod
    have hdata2 := typeOf_mul hgm (monicPoly_monic s)
    rw [htypeprod, htyg] at hdata2
    have hcancel : (typeOf (monicPoly s)).data = (typeOf R).data := by
      have h1 : (e', d) ::ₘ (typeOf (monicPoly s)).data
          = (e', d) ::ₘ (typeOf R).data := by
        have h2 : ({(e', d)} : Multiset (ℕ × ℕ)) + (typeOf (monicPoly s)).data
            = (e', d) ::ₘ (typeOf (monicPoly s)).data := Multiset.singleton_add _ _
        rw [← h2, ← hdata2, hdata]
      exact (Multiset.cons_inj_right _).mp h1
    show typeOf (monicPoly s) = typeOf R
    have heta1 : typeOf (monicPoly s) = ⟨(typeOf (monicPoly s)).data⟩ := rfl
    have heta2 : typeOf R = ⟨(typeOf R).data⟩ := rfl
    rw [heta1, heta2, hcancel]
  -- assemble
  have htyR : typeOf (monicPoly (fun i : Fin r => R.coeff (i : ℕ))) = typeOf R := by
    rw [hmpR]
  refine ⟨(fun i => g.coeff (i : ℕ)), (fun i => R.coeff (i : ℕ)),
    ⟨hpure, hcornerAt, hirrleaf⟩, hsteepρ, hmul, ?_, ?_⟩
  · rw [htyR]
    exact hdata
  · rw [htyR]
    exact hdecρ

/-- ★ **Off-type emptiness at general r**: if `(e', d) ∉ σ.data`, the sub-face cell at
frame `(h, e', d)` and cofactor mass `r` is EMPTY at every level. -/
theorem subfaceCell_gen_empty {π : O} (hπ : Irreducible π) {h e' d r : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d) (hr : 0 < r)
    {σ : FactorizationType} (hσ : (e', d) ∉ σ.data) (M : ℕ) :
    subfaceCell O π (e' * d + r) h e' d σ M
      = (∅ : Set (Coeff O (e' * d + r) (M + (e' * d + r)))) := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hc
  obtain ⟨a₁, a₂, -, -, -, hdata, -⟩ :=
    subfaceCell_factors_gen hπ hh1 hhe hcop hd0 hr hc
  refine hσ ?_
  rw [hdata]
  exact Multiset.mem_cons_self _ _

end Surjectivity

/-! ## §9 — THE SQUEEZE MEMBERSHIPS: the paired carrier set P sits between
(box) × (census at the shifted window) and (box) × (census at the full window) -/

section SqueezeMembership

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- Steepness lifts across windows: a class whose truncation is steep is steep. -/
private theorem steepCone_of_trunc {π : O} (hπ : Irreducible π) {h e' r : ℕ}
    (hh : 0 < h) (hhe : h < e') (hr : 0 < r) {v K : ℕ} (hvK : r + v ≤ K)
    {ρ : Coeff O r K}
    (hst : coeffFactor r (Nat.sub_le K v) ρ ∈ steepCone O r (K - v) h e') :
    ρ ∈ steepCone O r K h e' := by
  obtain ⟨a₂, rfl⟩ := proj_surjective O r K ρ
  rw [coeffFactor_proj] at hst
  intro j
  have hts : tSteep h e' r (j : ℕ) ≤ r := tSteep_le_mass hh hhe r _ hr
  have h1 : tSteep h e' r (j : ℕ) ≤ resOrd (proj O r (K - v) a₂ j) :=
    (tSteep_le_iff (by omega) h r (j : ℕ) _).mpr (hst j)
  have h2 : π ^ (tSteep h e' r (j : ℕ)) ∣ a₂ j := by
    have h3 : π ^ (resOrd (proj O r (K - v) a₂ j)) ∣ a₂ j :=
      (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le _ j) rfl j).mp le_rfl
    exact (pow_dvd_pow π h1).trans h3
  have h4 : tSteep h e' r (j : ℕ) ≤ resOrd (proj O r K a₂ j) :=
    (le_classCoeffVal_iff_dvd hπ (by omega) rfl j).mpr h2
  exact (tSteep_le_iff (by omega) h r (j : ℕ) _).mp h4

/-- **The box type is forced**: every lift of a pinned-box class has type
`⟨{(e', d)}⟩` (through the shifted spanning decision). -/
private theorem box_type_forced {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d)
    {K : ℕ} (hK2 : 2 * (h * d) < K) (hKm : e' * d + h * d ≤ K)
    {a₁ : Fin (e' * d) → O}
    (hγ : proj O (e' * d) K a₁ ∈ pinnedBox π K h e' d)
    (s₁ : Fin (e' * d) → O) (hs₁ : proj O (e' * d) K s₁ = proj O (e' * d) K a₁) :
    typeOf (monicPoly s₁) = ⟨{(e', d)}⟩ := by
  obtain ⟨hcone, hcorner, hirr⟩ := hγ
  have hdec₁ := box_decided_shifted_gen hπ hh hhe hcop hd0 (le_refl (h * d))
    (by omega) hKm hcone hcorner hirr
  have h1 : proj O (e' * d) (K - h * d) s₁ = proj O (e' * d) (K - h * d) a₁ := by
    have h2 := congrArg (coeffFactor (e' * d) (Nat.sub_le K (h * d))) hs₁
    rwa [coeffFactor_proj, coeffFactor_proj] at h2
  exact hdec₁ s₁ h1

/-- **The census membership of a carrier factor of a CELL point** (the squeeze's
upper leg): if the product of a pinned-box class and any class lands in the cell,
the cofactor class is decided-`τ` at the FULL window. -/
private theorem census_of_mem_cell {π : O} (hπ : Irreducible π) {h e' d r : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d) (hr : 0 < r)
    {σ τ : FactorizationType} (hσ : σ.data = (e', d) ::ₘ τ.data) {M : ℕ}
    (hM : 2 * (h * d * r) ≤ M)
    {γ : Coeff O (e' * d) (M + (e' * d + r))} {ρ : Coeff O r (M + (e' * d + r))}
    (hγ : γ ∈ pinnedBox π (M + (e' * d + r)) h e' d)
    (hcell : mulClass γ ρ ∈ subfaceCell O π (e' * d + r) h e' d σ M) :
    DecidedAt O r τ (M + (e' * d + r)) ρ := by
  obtain ⟨a₁, rfl⟩ := proj_surjective O (e' * d) (M + (e' * d + r)) γ
  obtain ⟨a₂, rfl⟩ := proj_surjective O r (M + (e' * d + r)) ρ
  have hh : 0 < h := hh1
  have hhd1 : 1 ≤ h * d := Nat.mul_pos hh hd0
  have hhdv : h * d ≤ h * d * r := Nat.le_mul_of_pos_right _ hr
  have hhd : h * d < e' * d := by
    have := (Nat.mul_lt_mul_right hd0).mpr hhe
    omega
  have hdecC : DecidedAt O (e' * d + r) σ (M + (e' * d + r))
      (mulClass (proj O (e' * d) (M + (e' * d + r)) a₁)
        (proj O r (M + (e' * d + r)) a₂)) := hcell.1.1.1.1.1
  intro s hs
  have hprodproj : proj O (e' * d + r) (M + (e' * d + r))
      (fun i => (monicPoly a₁ * monicPoly s).coeff (i : ℕ))
      = mulClass (proj O (e' * d) (M + (e' * d + r)) a₁)
          (proj O r (M + (e' * d + r)) a₂) := by
    rw [mulClass_proj, hs]
  have htypeprod := hdecC _ hprodproj
  have hmpF : monicPoly (fun i : Fin (e' * d + r) =>
      (monicPoly a₁ * monicPoly s).coeff (i : ℕ))
      = monicPoly a₁ * monicPoly s := by
    refine monicPoly_coeff_eq_self
      ((monicPoly_monic a₁).mul (monicPoly_monic s)) ?_
    rw [(monicPoly_monic a₁).natDegree_mul (monicPoly_monic s),
      monicPoly_natDegree, monicPoly_natDegree]
  rw [hmpF] at htypeprod
  have hty₁ : typeOf (monicPoly a₁) = ⟨{(e', d)}⟩ :=
    box_type_forced hπ hh hhe hcop hd0 (by omega) (by omega) hγ a₁ rfl
  have hdata2 := typeOf_mul (monicPoly_monic a₁) (monicPoly_monic s)
  rw [htypeprod, hty₁] at hdata2
  have hcancel : (typeOf (monicPoly s)).data = τ.data := by
    have h2 : ({(e', d)} : Multiset (ℕ × ℕ)) + (typeOf (monicPoly s)).data
        = (e', d) ::ₘ (typeOf (monicPoly s)).data := Multiset.singleton_add _ _
    have h1 : (e', d) ::ₘ (typeOf (monicPoly s)).data = (e', d) ::ₘ τ.data := by
      rw [← h2, ← hdata2, hσ]
    exact (Multiset.cons_inj_right _).mp h1
  show typeOf (monicPoly s) = τ
  have heta1 : typeOf (monicPoly s) = ⟨(typeOf (monicPoly s)).data⟩ := rfl
  have heta2 : τ = ⟨τ.data⟩ := rfl
  rw [heta1, heta2, hcancel]

end SqueezeMembership

/-! ## §10 — THE COUNT SQUEEZE:
`#box·(#census(K−v)·q^{rv}) ≤ #cell·q^v ≤ #box·#census(K)` at every level with
`2·h·d·r ≤ M` — the exact fiber identity `#P = #cell·q^v` through the general fiber
theorem, tiled below by the shifted census and capped above by the full census -/

section SqueezeCount

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **THE COUNT SQUEEZE** (exact at every level `M ≥ 2·h·d·r`, matched type). -/
private theorem card_cell_bounds {π : O} (hπ : Irreducible π) {h e' d r : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 0 < d) (hr : 0 < r)
    {σ τ : FactorizationType} (hσ : σ.data = (e', d) ::ₘ τ.data) {M : ℕ}
    (hM : 2 * (h * d * r) ≤ M) :
    Nat.card (pinnedBox π (M + (e' * d + r)) h e' d
          : Set (Coeff O (e' * d) (M + (e' * d + r))))
        * (Nat.card (steepDecCensus O r (M + (e' * d + r) - h * d * r) h e' τ)
            * residueCard O ^ (r * (h * d * r)))
      ≤ Nat.card (subfaceCell O π (e' * d + r) h e' d σ M)
          * residueCard O ^ (h * d * r)
    ∧ Nat.card (subfaceCell O π (e' * d + r) h e' d σ M)
          * residueCard O ^ (h * d * r)
      ≤ Nat.card (pinnedBox π (M + (e' * d + r)) h e' d
            : Set (Coeff O (e' * d) (M + (e' * d + r))))
          * Nat.card (steepDecCensus O r (M + (e' * d + r)) h e' τ) := by
  classical
  have hh : 0 < h := hh1
  have he'0 : 0 < e' := by omega
  have hn0 : 0 < e' * d := Nat.mul_pos he'0 hd0
  have hhd1 : 1 ≤ h * d := Nat.mul_pos hh hd0
  have hhdv : h * d ≤ h * d * r := Nat.le_mul_of_pos_right _ hr
  have hrv : r ≤ h * d * r := by
    have h2 : 1 * r ≤ (h * d) * r := Nat.mul_le_mul_right r hhd1
    omega
  letI : Fintype (Coeff O (e' * d) (M + (e' * d + r)) × Coeff O r (M + (e' * d + r))) :=
    Fintype.ofFinite _
  have hTfin : (subfaceCell O π (e' * d + r) h e' d σ M).Finite := Set.toFinite _
  have hKb : 2 * (h * d * r) + 1 ≤ M + (e' * d + r) := by omega
  -- THE IDENTITY: #P = #cell · q^v
  have hPeq : Nat.card (((pinnedBox π (M + (e' * d + r)) h e' d
          ×ˢ steepCone O r (M + (e' * d + r)) h e')
        ∩ (fun p : Coeff O (e' * d) (M + (e' * d + r))
            × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) ⁻¹'
          (subfaceCell O π (e' * d + r) h e' d σ M))
      : Set (Coeff O (e' * d) (M + (e' * d + r)) × Coeff O r (M + (e' * d + r))))
      = Nat.card (subfaceCell O π (e' * d + r) h e' d σ M)
          * residueCard O ^ (h * d * r) := by
    rw [natCard_eq_sum_fiber _ (fun p : Coeff O (e' * d) (M + (e' * d + r))
        × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) hTfin.toFinset
      (fun p hp => by
        rw [Set.Finite.mem_toFinset]
        exact hp.2)]
    have hfib : ∀ c ∈ hTfin.toFinset,
        Nat.card ((((pinnedBox π (M + (e' * d + r)) h e' d
              ×ˢ steepCone O r (M + (e' * d + r)) h e')
            ∩ (fun p : Coeff O (e' * d) (M + (e' * d + r))
                × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) ⁻¹'
              (subfaceCell O π (e' * d + r) h e' d σ M))
          ∩ (fun p : Coeff O (e' * d) (M + (e' * d + r))
              × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) ⁻¹' {c})
          : Set (Coeff O (e' * d) (M + (e' * d + r)) × Coeff O r (M + (e' * d + r))))
        = residueCard O ^ (h * d * r) := by
      intro c hc
      rw [Set.Finite.mem_toFinset] at hc
      obtain ⟨a₁, a₂, hbox, hsteep, hmul, -, -⟩ :=
        subfaceCell_factors_gen hπ hh1 hhe hcop hd0 hr hc
      have hset : (((pinnedBox π (M + (e' * d + r)) h e' d
              ×ˢ steepCone O r (M + (e' * d + r)) h e')
            ∩ (fun p : Coeff O (e' * d) (M + (e' * d + r))
                × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) ⁻¹'
              (subfaceCell O π (e' * d + r) h e' d σ M))
          ∩ (fun p : Coeff O (e' * d) (M + (e' * d + r))
              × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) ⁻¹' {c})
          = (pinnedBox π (M + (e' * d + r)) h e' d
              ×ˢ steepCone O r (M + (e' * d + r)) h e')
            ∩ (fun p : Coeff O (e' * d) (M + (e' * d + r))
                × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) ⁻¹'
              {mulClass (proj O (e' * d) (M + (e' * d + r)) a₁)
                (proj O r (M + (e' * d + r)) a₂)} := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨hp1, -⟩, hp2⟩
          exact ⟨hp1, hp2.trans hmul.symm⟩
        · rintro ⟨hp1, hp2⟩
          refine ⟨⟨hp1, ?_⟩, hp2.trans hmul⟩
          rw [hp2, hmul]
          exact hc
      rw [hset, fiber_eq_pairNbhd_gen hπ hh hhe hd0 hr hKb hbox hsteep]
      obtain ⟨hcone, hcorner, -⟩ := hbox
      have hcorner' : resOrd (proj O (e' * d) (M + (e' * d + r)) a₁ ⟨0, hn0⟩)
          = h * d := by
        rw [← resAt_lt (proj O (e' * d) (M + (e' * d + r)) a₁) hn0]
        exact hcorner
      exact natCard_pairNbhd_of_cones hπ he'0 hd0 hr hKb hcone hcorner'
        (fun j => hsteep j)
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hTfin]
  constructor
  · -- THE LOWER BOUND: box × (truncation-fibered shifted census) ⊆ P
    have hsubL : (pinnedBox π (M + (e' * d + r)) h e' d
          ×ˢ ((coeffFactor r (Nat.sub_le (M + (e' * d + r)) (h * d * r))) ⁻¹'
            (steepDecCensus O r (M + (e' * d + r) - h * d * r) h e' τ)))
        ⊆ ((pinnedBox π (M + (e' * d + r)) h e' d
            ×ˢ steepCone O r (M + (e' * d + r)) h e')
          ∩ (fun p : Coeff O (e' * d) (M + (e' * d + r))
              × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) ⁻¹'
            (subfaceCell O π (e' * d + r) h e' d σ M)) := by
      rintro ⟨γ, ρ⟩ ⟨hγ, hρ⟩
      have hsteepK : ρ ∈ steepCone O r (M + (e' * d + r)) h e' :=
        steepCone_of_trunc hπ hh hhe hr (by omega) hρ.1
      refine ⟨⟨hγ, hsteepK⟩, ?_⟩
      obtain ⟨a₁, rfl⟩ := proj_surjective O (e' * d) (M + (e' * d + r)) γ
      obtain ⟨a₂, rfl⟩ := proj_surjective O r (M + (e' * d + r)) ρ
      have hdec₂ : DecidedAt O r τ (M + (e' * d + r) - h * d * r)
          (proj O r (M + (e' * d + r) - h * d * r) a₂) := by
        have h1 := hρ.2
        rwa [coeffFactor_proj] at h1
      exact mul_mem_subfaceCell_gen hπ hh1 hhe hcop hd0 hr hσ hM hγ hsteepK hdec₂
    have hcardL : Nat.card ((pinnedBox π (M + (e' * d + r)) h e' d
          ×ˢ ((coeffFactor r (Nat.sub_le (M + (e' * d + r)) (h * d * r))) ⁻¹'
            (steepDecCensus O r (M + (e' * d + r) - h * d * r) h e' τ)))
        : Set (Coeff O (e' * d) (M + (e' * d + r)) × Coeff O r (M + (e' * d + r))))
        = Nat.card (pinnedBox π (M + (e' * d + r)) h e' d
            : Set (Coeff O (e' * d) (M + (e' * d + r))))
          * (Nat.card (steepDecCensus O r (M + (e' * d + r) - h * d * r) h e' τ)
              * residueCard O ^ (r * (h * d * r))) := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
      congr 1
      have h1 := card_preimage_coeffFactor_eq (O := O) r
        (Nat.sub_le (M + (e' * d + r)) (h * d * r))
        (steepDecCensus O r (M + (e' * d + r) - h * d * r) h e' τ)
      have h2 : M + (e' * d + r) - (M + (e' * d + r) - h * d * r) = h * d * r := by
        omega
      rw [h2] at h1
      exact h1
    have hmono : Nat.card ((pinnedBox π (M + (e' * d + r)) h e' d
          ×ˢ ((coeffFactor r (Nat.sub_le (M + (e' * d + r)) (h * d * r))) ⁻¹'
            (steepDecCensus O r (M + (e' * d + r) - h * d * r) h e' τ)))
        : Set (Coeff O (e' * d) (M + (e' * d + r)) × Coeff O r (M + (e' * d + r))))
        ≤ Nat.card (((pinnedBox π (M + (e' * d + r)) h e' d
            ×ˢ steepCone O r (M + (e' * d + r)) h e')
          ∩ (fun p : Coeff O (e' * d) (M + (e' * d + r))
              × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) ⁻¹'
            (subfaceCell O π (e' * d + r) h e' d σ M))
        : Set (Coeff O (e' * d) (M + (e' * d + r)) × Coeff O r (M + (e' * d + r)))) := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hsubL (Set.toFinite _)
    rw [hcardL, hPeq] at hmono
    exact hmono
  · -- THE UPPER BOUND: P ⊆ box × (full-window census)
    have hsubU : ((pinnedBox π (M + (e' * d + r)) h e' d
            ×ˢ steepCone O r (M + (e' * d + r)) h e')
          ∩ (fun p : Coeff O (e' * d) (M + (e' * d + r))
              × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) ⁻¹'
            (subfaceCell O π (e' * d + r) h e' d σ M))
        ⊆ (pinnedBox π (M + (e' * d + r)) h e' d
            ×ˢ steepDecCensus O r (M + (e' * d + r)) h e' τ) := by
      rintro ⟨γ, ρ⟩ ⟨⟨hγ, hρ⟩, hcell⟩
      exact ⟨hγ, hρ, census_of_mem_cell hπ hh1 hhe hcop hd0 hr hσ hM hγ hcell⟩
    have hcardU : Nat.card ((pinnedBox π (M + (e' * d + r)) h e' d
          ×ˢ steepDecCensus O r (M + (e' * d + r)) h e' τ)
        : Set (Coeff O (e' * d) (M + (e' * d + r)) × Coeff O r (M + (e' * d + r))))
        = Nat.card (pinnedBox π (M + (e' * d + r)) h e' d
            : Set (Coeff O (e' * d) (M + (e' * d + r))))
          * Nat.card (steepDecCensus O r (M + (e' * d + r)) h e' τ) := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
    have hmono : Nat.card (((pinnedBox π (M + (e' * d + r)) h e' d
            ×ˢ steepCone O r (M + (e' * d + r)) h e')
          ∩ (fun p : Coeff O (e' * d) (M + (e' * d + r))
              × Coeff O r (M + (e' * d + r)) => mulClass p.1 p.2) ⁻¹'
            (subfaceCell O π (e' * d + r) h e' d σ M))
        : Set (Coeff O (e' * d) (M + (e' * d + r)) × Coeff O r (M + (e' * d + r))))
        ≤ Nat.card ((pinnedBox π (M + (e' * d + r)) h e' d
            ×ˢ steepDecCensus O r (M + (e' * d + r)) h e' τ)
          : Set (Coeff O (e' * d) (M + (e' * d + r)) × Coeff O r (M + (e' * d + r)))) := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hsubU (Set.toFinite _)
    rw [hcardU, hPeq] at hmono
    exact hmono

end SqueezeCount

/-! ## §11 — ★★★ THE CONDITIONAL LAW: `SteepDecCensusLaw` at the frame's cofactor data
implies `SubfaceFrameLaw` — the analytic squeeze closes with value
`nz_d(q)·L_τ(q)/q^{wLeaf + h·d·r}` -/

section Law

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★★ **THE PER-FRAME LAW FROM THE CENSUS LAW** (every frame, every `r ≥ 1`): the
steep decided census law at the frame's cofactor data `(r, h, e', τ)` — with
`τ = σ minus the block entry` — implies `SubfaceFrameLaw m h e' d σ`.  The value is
`nz_d(q)·(n_τ/d_τ)(q)/q^{wLeaf + h·d·r}`; at unmatched `σ` the cell is empty and the
law is the zero family.  With SFW's `subfaceFrameLaw_r_one` this re-bases the leaf
row's ENTIRE frame family onto the census family. -/
theorem subfaceFrameLaw_of_steepCensus (m h e' d r : ℕ) (σ : FactorizationType)
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 1 ≤ d) (hr : 1 ≤ r)
    (hm : m = e' * d + r)
    (hcensus : SteepDecCensusLaw r h e' ⟨σ.data.erase (e', d)⟩) :
    SubfaceFrameLaw m h e' d σ := by
  subst hm
  have hh : 0 < h := hh1
  have he'0 : 0 < e' := by omega
  have hd0' : 0 < d := hd0
  have hr' : 0 < r := hr
  by_cases hσc : (e', d) ∈ σ.data
  · -- THE MATCHED TYPE: the squeeze
    have hσeq : σ.data = (e', d) ::ₘ (⟨σ.data.erase (e', d)⟩ : FactorizationType).data :=
      (Multiset.cons_erase hσc).symm
    obtain ⟨nc, dc, hdc0, hcen⟩ := hcensus
    refine ⟨nzPoly d * nc, Polynomial.X ^ (wLeaf h e' d + h * d * r) * dc,
      mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hdc0, ?_⟩
    intro O _ _ _ _ _
    obtain ⟨hdcO, hcenO⟩ := hcen O
    letI : Fintype (IsLocalRing.ResidueField O) := Fintype.ofFinite _
    have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
    have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hq0 : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    have hden : (Polynomial.X ^ (wLeaf h e' d + h * d * r) * dc : Polynomial ℚ).eval
        ((residueCard O : ℕ) : ℚ) ≠ 0 := by
      rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      exact mul_ne_zero (pow_ne_zero _ hqQ) hdcO
    refine ⟨hden, ?_⟩
    intro π hπ
    have hlim := hcenO π hπ
    have hqcard : residueCard O = Fintype.card (IsLocalRing.ResidueField O) :=
      Nat.card_eq_fintype_card
    -- the limit value
    have hval : ((((nzPoly d * nc).eval ((residueCard O : ℕ) : ℚ))
          / ((Polynomial.X ^ (wLeaf h e' d + h * d * r) * dc).eval
              ((residueCard O : ℕ) : ℚ)) : ℚ) : ℝ)
        = ((Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d * r))
          * ((nc.eval ((residueCard O : ℕ) : ℚ)
              / dc.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) := by
      rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X]
      have hnum : (nzPoly d).eval ((residueCard O : ℕ) : ℚ)
          = (Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℚ) := by
        rw [hqcard]
        exact nzPoly_eval_card (IsLocalRing.ResidueField O) hd0
      rw [hnum]
      push_cast
      ring
    rw [hval]
    -- the two bounding sequences and their limits
    have hφlow : Filter.Tendsto (fun M : ℕ => M + e' * d - h * d * r)
        Filter.atTop Filter.atTop :=
      (tendsto_sub_atTop_nat _).comp (tendsto_add_atTop_nat _)
    have hφupp : Filter.Tendsto (fun M : ℕ => M + e' * d)
        Filter.atTop Filter.atTop := tendsto_add_atTop_nat _
    have hlow : Filter.Tendsto (fun M : ℕ =>
        ((Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d * r))
          * ((Nat.card (steepDecCensus O r ((M + e' * d - h * d * r) + r) h e'
                ⟨σ.data.erase (e', d)⟩) : ℝ)
              / ((residueCard O : ℕ) : ℝ) ^ (r * ((M + e' * d - h * d * r) + r))))
        Filter.atTop
        (nhds (((Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d * r))
          * ((nc.eval ((residueCard O : ℕ) : ℚ)
              / dc.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))) :=
      (hlim.comp hφlow).const_mul _
    have hupp : Filter.Tendsto (fun M : ℕ =>
        ((Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d * r))
          * ((Nat.card (steepDecCensus O r ((M + e' * d) + r) h e'
                ⟨σ.data.erase (e', d)⟩) : ℝ)
              / ((residueCard O : ℕ) : ℝ) ^ (r * ((M + e' * d) + r))))
        Filter.atTop
        (nhds (((Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d * r))
          * ((nc.eval ((residueCard O : ℕ) : ℚ)
              / dc.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ))) :=
      (hlim.comp hφupp).const_mul _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
    · -- LOW ≤ the normalized cell count, eventually
      refine Filter.eventually_atTop.mpr ⟨2 * (h * d * r), fun M hMge => ?_⟩
      have hbounds := card_cell_bounds hπ hh1 hhe hcop hd0' hr' hσeq (M := M) hMge
      have hhd : h * d < e' * d := by
        have := (Nat.mul_lt_mul_right hd0').mpr hhe
        omega
      have hboxcard := card_pinnedBox (π := π) hπ hh hhe hd0'
        (by omega : e' * d ≤ M + (e' * d + r))
        (by omega : h * d < M + (e' * d + r))
      have hNat1 := hbounds.1
      rw [hboxcard] at hNat1
      have hR := (Nat.cast_le (α := ℝ)).mpr hNat1
      push_cast at hR
      have hidx : (M + e' * d - h * d * r) + r = M + (e' * d + r) - h * d * r := by
        omega
      rw [hidx]
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have hexpL : ((residueCard O : ℕ) : ℝ) ^ (e' * d * (M + (e' * d + r)) - wLeaf h e' d)
            * ((residueCard O : ℕ) : ℝ) ^ (r * (h * d * r))
            * ((residueCard O : ℕ) : ℝ)
                ^ (wLeaf h e' d + r * (M + (e' * d + r) - h * d * r))
          = ((residueCard O : ℕ) : ℝ) ^ ((e' * d + r) * (M + (e' * d + r))) := by
        rw [← pow_add, ← pow_add]
        congr 1
        have hwle : wLeaf h e' d ≤ e' * d * (M + (e' * d + r)) := by
          have h1 := wLeaf_le_sq (h := h) (e' := e') (d := d) hh hhe hd0'
          have h2 : (e' * d) * (e' * d) ≤ (e' * d) * (M + (e' * d + r)) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        have hrsplit : r * (M + (e' * d + r) - h * d * r) + r * (h * d * r)
            = r * (M + (e' * d + r)) := by
          rw [← Nat.mul_add]
          congr 1
          omega
        have hmsplit : (e' * d + r) * (M + (e' * d + r))
            = e' * d * (M + (e' * d + r)) + r * (M + (e' * d + r)) := by ring
        omega
      have hexpR : ((residueCard O : ℕ) : ℝ) ^ (h * d * r)
            * ((residueCard O : ℕ) : ℝ)
                ^ (wLeaf h e' d + r * (M + (e' * d + r) - h * d * r))
          = ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d * r)
            * ((residueCard O : ℕ) : ℝ) ^ (r * (M + (e' * d + r) - h * d * r)) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      calc (Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
            * (Nat.card (steepDecCensus O r (M + (e' * d + r) - h * d * r) h e'
                ⟨σ.data.erase (e', d)⟩) : ℝ)
            * ((residueCard O : ℕ) : ℝ) ^ ((e' * d + r) * (M + (e' * d + r)))
          = (Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
              * ((residueCard O : ℕ) : ℝ)
                  ^ (e' * d * (M + (e' * d + r)) - wLeaf h e' d)
              * ((Nat.card (steepDecCensus O r (M + (e' * d + r) - h * d * r) h e'
                  ⟨σ.data.erase (e', d)⟩) : ℝ)
                * ((residueCard O : ℕ) : ℝ) ^ (r * (h * d * r)))
              * ((residueCard O : ℕ) : ℝ)
                  ^ (wLeaf h e' d + r * (M + (e' * d + r) - h * d * r)) := by
            rw [← hexpL]
            ring
        _ ≤ (Nat.card (subfaceCell O π (e' * d + r) h e' d σ M) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ (h * d * r)
              * ((residueCard O : ℕ) : ℝ)
                  ^ (wLeaf h e' d + r * (M + (e' * d + r) - h * d * r)) := by
            exact mul_le_mul_of_nonneg_right hR (by positivity)
        _ = (Nat.card (subfaceCell O π (e' * d + r) h e' d σ M) : ℝ)
              * (((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d * r)
                * ((residueCard O : ℕ) : ℝ) ^ (r * (M + (e' * d + r) - h * d * r))) := by
            rw [← hexpR]
            ring
    · -- the normalized cell count ≤ UP, eventually
      refine Filter.eventually_atTop.mpr ⟨2 * (h * d * r), fun M hMge => ?_⟩
      have hbounds := card_cell_bounds hπ hh1 hhe hcop hd0' hr' hσeq (M := M) hMge
      have hhd : h * d < e' * d := by
        have := (Nat.mul_lt_mul_right hd0').mpr hhe
        omega
      have hboxcard := card_pinnedBox (π := π) hπ hh hhe hd0'
        (by omega : e' * d ≤ M + (e' * d + r))
        (by omega : h * d < M + (e' * d + r))
      have hNat2 := hbounds.2
      rw [hboxcard] at hNat2
      have hR := (Nat.cast_le (α := ℝ)).mpr hNat2
      push_cast at hR
      have hidx : (M + e' * d) + r = M + (e' * d + r) := by omega
      rw [hidx]
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      have hexpL : ((residueCard O : ℕ) : ℝ) ^ (h * d * r)
            * ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + r * (M + (e' * d + r)))
          = ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d * r)
            * ((residueCard O : ℕ) : ℝ) ^ (r * (M + (e' * d + r))) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      have hexpR : ((residueCard O : ℕ) : ℝ)
              ^ (e' * d * (M + (e' * d + r)) - wLeaf h e' d)
            * ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + r * (M + (e' * d + r)))
          = ((residueCard O : ℕ) : ℝ) ^ ((e' * d + r) * (M + (e' * d + r))) := by
        rw [← pow_add]
        congr 1
        have hwle : wLeaf h e' d ≤ e' * d * (M + (e' * d + r)) := by
          have h1 := wLeaf_le_sq (h := h) (e' := e') (d := d) hh hhe hd0'
          have h2 : (e' * d) * (e' * d) ≤ (e' * d) * (M + (e' * d + r)) :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        have hmsplit : (e' * d + r) * (M + (e' * d + r))
            = e' * d * (M + (e' * d + r)) + r * (M + (e' * d + r)) := by ring
        omega
      calc (Nat.card (subfaceCell O π (e' * d + r) h e' d σ M) : ℝ)
            * (((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + h * d * r)
              * ((residueCard O : ℕ) : ℝ) ^ (r * (M + (e' * d + r))))
          = (Nat.card (subfaceCell O π (e' * d + r) h e' d σ M) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ (h * d * r)
              * ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + r * (M + (e' * d + r))) := by
            rw [← hexpL]
            ring
        _ ≤ (Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
              * ((residueCard O : ℕ) : ℝ)
                  ^ (e' * d * (M + (e' * d + r)) - wLeaf h e' d)
              * (Nat.card (steepDecCensus O r (M + (e' * d + r)) h e'
                  ⟨σ.data.erase (e', d)⟩) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d + r * (M + (e' * d + r))) := by
            exact mul_le_mul_of_nonneg_right hR (by positivity)
        _ = (Nat.card (nzGenre (IsLocalRing.ResidueField O) d) : ℝ)
              * (Nat.card (steepDecCensus O r (M + (e' * d + r)) h e'
                  ⟨σ.data.erase (e', d)⟩) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ ((e' * d + r) * (M + (e' * d + r))) := by
            rw [← hexpR]
            ring
  · -- THE MISMATCHED TYPE: the cell is empty at every level
    refine ZcURLim_zero.congr ?_
    intro O _ _ _ _ _ π hπ M
    have hempty := subfaceCell_gen_empty hπ hh1 hhe hcop hd0' hr' hσc M
    show (0 : ℝ) = (Nat.card (subfaceCell O π (e' * d + r) h e' d σ M) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ ((e' * d + r) * (M + (e' * d + r)))
    rw [hempty]
    simp

end Law

/-! ## §12 — THE MASTERS RECOMPUTED: the leaf row's r ≥ 2 premise re-based from
`SubfaceFrameLaw` onto the strictly finer `SteepDecCensusLaw` family (a discharge-path
refinement in LSF §4's sanctioned genre; the r = 1 members stay SFW's theorems) -/

section Masters

open Uniformity.Density.IFCG69 (decidedSliceAt_all_of_visCensus_frames_r2
  decidedSliceAt_all_of_MASTER_FRAMES_r2 capstoneHypotheses_of_MASTER_FRAMES_r2)

/-- ★★ **The full frame family from the census family**: `SubfaceFrameLaw` at EVERY
admissible frame follows from the steep decided census laws at the r ≥ 2 frames alone
(r = 1: SFW's unconditional theorem; r ≥ 2: this file's conditional law). -/
theorem subfaceFrameLaws_of_censusLaws (m : ℕ) (σ : FactorizationType)
    (hcensus : ∀ p ∈ subFrames m σ, m ≠ p.2.1 * p.2.2 + 1 →
      SteepDecCensusLaw (m - p.2.1 * p.2.2) p.1 p.2.1 ⟨σ.data.erase (p.2.1, p.2.2)⟩) :
    ∀ p ∈ subFrames m σ, SubfaceFrameLaw m p.1 p.2.1 p.2.2 σ := by
  intro p hp
  obtain ⟨hh1, hhe, hcop, hd1, hdm, hmem⟩ := mem_subFrames_iff.mp hp
  by_cases heq : m = p.2.1 * p.2.2 + 1
  · exact subfaceFrameLaw_r_one m p.1 p.2.1 p.2.2 σ hh1 hhe hcop hd1 heq
  · exact subfaceFrameLaw_of_steepCensus m p.1 p.2.1 p.2.2 (m - p.2.1 * p.2.2) σ
      hh1 hhe hcop hd1 (by omega) (by omega) (hcensus p hp heq)

/-- ★★★ **THE CENSUS MASTER ON PCD's SPINE, LEAF ROW ON THE CENSUS FAMILY**. -/
theorem decidedSliceAt_all_of_visCensus_census
    (hVC : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ∀ g, VisCensusLaw g e σ)
    (hPF : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerFullSpanLaw e σ)
    (hCensus : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ p ∈ subFrames e σ, e ≠ p.2.1 * p.2.2 + 1 →
          SteepDecCensusLaw (e - p.2.1 * p.2.2) p.1 p.2.1
            ⟨σ.data.erase (p.2.1, p.2.2)⟩)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_visCensus_frames_r2 hVC hPF
    (fun e he hsm σ hσ hwit hram hcard p hp hne => by
      obtain ⟨hh1, hhe, hcop, hd1, hdm, hmem⟩ := mem_subFrames_iff.mp hp
      exact subfaceFrameLaw_of_steepCensus e p.1 p.2.1 p.2.2 (e - p.2.1 * p.2.2) σ
        hh1 hhe hcop hd1 (by omega) (by omega)
        (hCensus e he hsm σ hσ hwit hram hcard p hp hne))
    hR4

/-- ★★★ **THE CENSUS MASTER ON LSC's SPINE, LEAF ROW ON THE CENSUS FAMILY**: the
surviving premise surface is {`FactorCorrespondenceAt` (THE staged cite),
`EisFullSpanRemainderLaw`, `SplitConvolutionDefectLaw`, `PowerConvolutionDefectLaw`,
`SteepDecCensusLaw (e − e'·d) h e' τ` at the admissible frames with `e ≠ e'·d + 1`}. -/
theorem decidedSliceAt_all_of_MASTER_CENSUS
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
    (hCensus : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ p ∈ subFrames e σ, e ≠ p.2.1 * p.2.2 + 1 →
          SteepDecCensusLaw (e - p.2.1 * p.2.2) p.1 p.2.1
            ⟨σ.data.erase (p.2.1, p.2.2)⟩) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_MASTER_FRAMES_r2 hFC hEis hSD hPD
    (fun e he hsm σ hσ hwit hram hcard p hp hne => by
      obtain ⟨hh1, hhe, hcop, hd1, hdm, hmem⟩ := mem_subFrames_iff.mp hp
      exact subfaceFrameLaw_of_steepCensus e p.1 p.2.1 p.2.2 (e - p.2.1 * p.2.2) σ
        hh1 hhe hcop hd1 (by omega) (by omega)
        (hCensus e he hsm σ hσ hwit hram hcard p hp hne))

universe uW uG uKt uL

/-- ★★★ **THE CAPSTONE MASTER, LEAF ROW ON THE CENSUS FAMILY** (ID12's honesty frame
applies verbatim). -/
theorem capstoneHypotheses_of_MASTER_CENSUS (n : ℕ)
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
    (hCensus : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
        ∀ p ∈ subFrames e σ, e ≠ p.2.1 * p.2.2 + 1 →
          SteepDecCensusLaw (e - p.2.1 * p.2.2) p.1 p.2.1
            ⟨σ.data.erase (p.2.1, p.2.2)⟩) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  capstoneHypotheses_of_MASTER_FRAMES_r2.{uW, uG, uKt, uL} n
    hladder hdeepTwist hFC hEis hSD hPD
    (fun e he hsm σ hσ hwit hram hcard p hp hne => by
      obtain ⟨hh1, hhe, hcop, hd1, hdm, hmem⟩ := mem_subFrames_iff.mp hp
      exact subfaceFrameLaw_of_steepCensus e p.1 p.2.1 p.2.2 (e - p.2.1 * p.2.2) σ
        hh1 hhe hcop hd1 (by omega) (by omega)
        (hCensus e he hsm σ hσ hwit hram hcard p hp hne))

end Masters

/-! ## §13 — NONVACUITY: the census family's first member — `SteepDecCensusLaw` at
`r = 1` is a THEOREM (the mass-1 strict cone is SFW's `steepLin`; decidedness is
outright), and the conditional law reproduces SFW's witness frame through it -/

section CensusOne

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The mass-1 steep decided census IS `steepLin` (steepness `⟺` the X-stratum under
`h < e'`; every mass-1 class is decided `⟨{(1,1)}⟩`). -/
private theorem steepDecCensus_one_eq (h e' : ℕ) (hh1 : 1 ≤ h) (hhe : h < e') (K : ℕ) :
    steepDecCensus O 1 K h e' ⟨{(1, 1)}⟩ = steepLin O K := by
  ext ρ
  constructor
  · rintro ⟨hst, -⟩
    have h1 := hst 0
    have h2 : h * (1 - ((0 : Fin 1) : ℕ)) = h := by norm_num
    rw [h2] at h1
    show 1 ≤ resOrd (ρ 0)
    rcases Nat.eq_zero_or_pos (resOrd (ρ 0)) with h3 | h3
    · rw [h3, Nat.mul_zero] at h1
      omega
    · exact h3
  · intro hst
    refine ⟨?_, decidedAt_linear ρ⟩
    intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    have h2 : e' * 1 ≤ e' * resOrd (ρ 0) := Nat.mul_le_mul_left e' hst
    have h3 : h * (1 - ((0 : Fin 1) : ℕ)) = h := by norm_num
    rw [h3]
    omega

/-- ★ **THE r = 1 CENSUS LAW, unconditional**: `SteepDecCensusLaw 1 h e' ⟨{(1,1)}⟩`
with value `1/q` — the census family's first member is closed, so the family is
non-vacuous and the conditional law's premise is honest. -/
theorem steepDecCensusLaw_one (h e' : ℕ) (hh1 : 1 ≤ h) (hhe : h < e') :
    SteepDecCensusLaw 1 h e' ⟨{(1, 1)}⟩ := by
  refine ⟨1, Polynomial.X, Polynomial.X_ne_zero, ?_⟩
  intro O _ _ _ _ _
  have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
  have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨by rw [Polynomial.eval_X]; exact hqQ, ?_⟩
  intro π hπ
  have hval : (((Polynomial.eval ((residueCard O : ℕ) : ℚ) (1 : Polynomial ℚ)
        / Polynomial.eval ((residueCard O : ℕ) : ℚ) (Polynomial.X : Polynomial ℚ)) : ℚ) : ℝ)
      = 1 / ((residueCard O : ℕ) : ℝ) := by
    rw [Polynomial.eval_one, Polynomial.eval_X]
    push_cast
    ring
  rw [hval]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventuallyEq_of_mem (Filter.Ici_mem_atTop 0) fun M _ => ?_
  show (1 : ℝ) / ((residueCard O : ℕ) : ℝ)
      = (Nat.card (steepDecCensus O 1 (M + 1) h e' ⟨{(1, 1)}⟩) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (1 * (M + 1))
  rw [steepDecCensus_one_eq h e' hh1 hhe, card_steepLin hπ (by omega : 1 ≤ M + 1)]
  rw [div_eq_div_iff hqR (pow_ne_zero _ hqR)]
  push_cast
  rw [one_mul, ← pow_succ]
  congr 1
  omega

/-- ★ **REGRESSION**: the conditional law + the r = 1 census law REPRODUCE SFW's
closed witness frame `(3, 4, 1)` at `m = 5` — a decorrelated check that the squeeze's
value plumbing agrees with the exact r = 1 computation. -/
example : SubfaceFrameLaw 5 3 4 1 ⟨{(4, 1), (1, 1)}⟩ := by
  refine subfaceFrameLaw_of_steepCensus 5 3 4 1 1 _ (by omega) (by omega) (by decide)
    (by omega) (by omega) (by omega) ?_
  show SteepDecCensusLaw 1 3 4
    ⟨(({(4, 1), (1, 1)} : Multiset (ℕ × ℕ))).erase (4, 1)⟩
  have herase : (({(4, 1), (1, 1)} : Multiset (ℕ × ℕ))).erase (4, 1)
      = {(1, 1)} := by decide
  rw [herase]
  exact steepDecCensusLaw_one 3 4 (by omega) (by omega)

end CensusOne

/-! ## §14 — ★★ THE SPECIAL-FRAME FIRE: at the frames with `r·(e' − h) ≤ e'` the
strict cone IS the integer slope-1 box, the coordinate scaling `X ↦ πX` preserves
types, and the census law FOLLOWS from `DecidedValueLaw r τ` — SubfaceFrameLaw fires
at these r ≥ 2 frames conditional on ONE smaller-mass value law -/

section SpecialFire

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- `∑_{j<r} (r − j) = bigTLoop r`. -/
private theorem sum_fin_sub_eq_bigTLoop (r : ℕ) :
    (∑ t : Fin r, (r - (t : ℕ))) = bigTLoop r := by
  rw [Fin.sum_univ_eq_sum_range]
  have h1 : ∑ t ∈ Finset.range r, (r - t) = ∑ t ∈ Finset.range r, (t + 1) := by
    have h2 := Finset.sum_range_reflect (fun i => i + 1) r
    rw [← h2]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_range] at ht
    omega
  rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one, ← kappaLoop_eq_sum, bigTLoop_eq_kappaLoop_add]

/-- The same-window coordinate scaling `u_t ↦ π^{κ t}·u_t` (IFCG51's private replica). -/
private def scaledHom (α : O) {D : ℕ} (K : ℕ) (κ : Fin D → ℕ) :
    Coeff O D K →+ Coeff O D K where
  toFun u := fun t => Ideal.Quotient.mk ((maximalIdeal O) ^ K) (α ^ κ t) * u t
  map_zero' := by
    funext t
    simp
  map_add' u v := by
    funext t
    simp [mul_add]

private theorem scaledHom_apply (α : O) {D : ℕ} (K : ℕ) (κ : Fin D → ℕ)
    (u : Coeff O D K) (t : Fin D) :
    scaledHom α K κ u t
      = Ideal.Quotient.mk ((maximalIdeal O) ^ K) (α ^ κ t) * u t := rfl

/-- The scaled image's range is exactly the `κ`-divisibility box (IFCG51's private
replica). -/
private theorem mem_range_scaledHom {α : O} (hα : Irreducible α) {D K : ℕ}
    (κ : Fin D → ℕ) (hκ : ∀ t, κ t ≤ K) (b : Coeff O D K) :
    b ∈ Set.range (scaledHom α K κ) ↔ ∀ t, κ t ≤ resOrd (b t) := by
  constructor
  · rintro ⟨u, rfl⟩ t
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u t)
    rw [scaledHom_apply, ← hy, ← map_mul]
    exact (resOrd_ge_iff hα (hκ t) _).mpr (dvd_mul_right _ _)
  · intro hb
    have hx : ∀ t, ∃ x : O,
        Ideal.Quotient.mk ((maximalIdeal O) ^ K) (α ^ κ t * x) = b t := by
      intro t
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (b t)
      have hdvd : α ^ κ t ∣ y :=
        (resOrd_ge_iff hα (hκ t) y).mp (by rw [hy]; exact hb t)
      obtain ⟨x, hxeq⟩ := hdvd
      exact ⟨x, by rw [← hxeq, hy]⟩
    choose x hx using hx
    refine ⟨proj O D K x, ?_⟩
    funext t
    rw [scaledHom_apply]
    show Ideal.Quotient.mk ((maximalIdeal O) ^ K) (α ^ κ t)
        * Ideal.Quotient.mk ((maximalIdeal O) ^ K) (x t) = b t
    rw [← map_mul]
    exact hx t

/-- The scaled map's kernel count: `q^(Σ κ)` (IFCG51's private replica). -/
private theorem card_ker_scaledHom {α : O} (hα : Irreducible α) {D K : ℕ}
    (κ : Fin D → ℕ) (hκ : ∀ t, κ t ≤ K) :
    Nat.card (scaledHom (O := O) α K κ).ker = residueCard O ^ (∑ t, κ t) := by
  classical
  have hα0 : α ≠ 0 := hα.ne_zero
  have hset : ((scaledHom (O := O) α K κ).ker : Set (Coeff O D K))
      = {u : Coeff O D K | ∀ t, u t ∈ {x : Res O K | K - κ t ≤ resOrd x}} := by
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
  have hcong : Nat.card (scaledHom (O := O) α K κ).ker
      = Nat.card {u : Coeff O D K | ∀ t, u t ∈ {x : Res O K | K - κ t ≤ resOrd x}} :=
    Nat.card_congr (Equiv.setCongr hset)
  rw [hcong, card_pi_set]
  have hfac : ∀ t : Fin D,
      Nat.card ({x : Res O K | K - κ t ≤ resOrd x} : Set (Res O K))
        = residueCard O ^ (K - (K - κ t)) := fun t =>
    card_setOf_le_resOrd (by omega)
  rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have := hκ t
  omega

/-- Fibered preimage count over the image (IFCG51's private replica). -/
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

/-- **The special-frame box read**: under `r·(e'−h) ≤ e'`, the strict cone at
abscissa `j < r` forces the slope-1 divisibility `r − j ≤ v`. -/
private theorem special_box_read {h e' r : ℕ} (hhe : h < e')
    (hspec : r * (e' - h) ≤ e') {j v : ℕ} (hj : j < r)
    (hlt : h * (r - j) < e' * v) : r - j ≤ v := by
  by_contra hcon
  have hcon' : v < r - j := by omega
  have h1 : e' * v ≤ e' * (r - j - 1) := Nat.mul_le_mul_left e' (by omega)
  have h2 : (e' - h) * (r - j) ≤ (e' - h) * r := Nat.mul_le_mul_left _ (by omega)
  have h3 : (e' - h) * r = r * (e' - h) := Nat.mul_comm _ _
  have h4 : e' * (r - j) = h * (r - j) + (e' - h) * (r - j) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have h5 : e' * (r - j - 1) + e' = e' * (r - j) := by
    have h6 : (r - j - 1) + 1 = r - j := by omega
    calc e' * (r - j - 1) + e' = e' * ((r - j - 1) + 1) := by ring
      _ = e' * (r - j) := by rw [h6]
  omega

/-- **THE LOWER TRANSPORT**: a class whose level-`M` truncation is decided-`τ` scales
into the steep decided census at `M + r` — the scaling preserves types
(`typeOf_scaleVecN`), so every lift of the scaled class factors through a lift of the
decided truncation. -/
private theorem census_of_trunc_decided {π : O} (hπ : Irreducible π) {h e' r : ℕ}
    (hhe : h < e') (hr : 1 ≤ r)
    {M : ℕ} {τ : FactorizationType} {y : Coeff O r (M + r)}
    (hy : coeffFactor r (by omega : M ≤ M + r) y ∈ decidedSet O r τ M) :
    scaledHom π (M + r) (fun j : Fin r => r - (j : ℕ)) y
      ∈ steepDecCensus O r (M + r) h e' τ := by
  obtain ⟨y', rfl⟩ := proj_surjective O r (M + r) y
  rw [coeffFactor_proj] at hy
  have hΘ : scaledHom π (M + r) (fun j : Fin r => r - (j : ℕ)) (proj O r (M + r) y')
      = proj O r (M + r) (scaleVecN π y') := by
    funext t
    rw [scaledHom_apply]
    show Ideal.Quotient.mk ((maximalIdeal O) ^ (M + r)) (π ^ (r - (t : ℕ)))
        * Ideal.Quotient.mk ((maximalIdeal O) ^ (M + r)) (y' t)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ (M + r)) (scaleVecN π y' t)
    rw [← map_mul]
    rfl
  rw [hΘ]
  constructor
  · -- the strict cone
    intro j
    have hj : (j : ℕ) < r := j.isLt
    have hbox : (r - (j : ℕ)) ≤ resOrd (proj O r (M + r) (scaleVecN π y') j) := by
      refine (le_classCoeffVal_iff_dvd hπ (by omega : r - (j : ℕ) ≤ M + r) rfl j).mpr ?_
      exact ⟨y' j, rfl⟩
    have h1 : h * (r - (j : ℕ)) < e' * (r - (j : ℕ)) := by
      have := (Nat.mul_lt_mul_right (show 0 < r - (j : ℕ) by omega)).mpr hhe
      omega
    have h2 : e' * (r - (j : ℕ)) ≤ e' * resOrd (proj O r (M + r) (scaleVecN π y') j) :=
      Nat.mul_le_mul_left e' hbox
    omega
  · -- decided at the full window
    intro b hb
    have hdvdb := (proj_eq_iff_dvd hπ _ _).1 hb
    have hfac : ∀ j : Fin r, π ^ (r - (j : ℕ)) ∣ b j := by
      intro j
      have h1 : π ^ (r - (j : ℕ)) ∣ π ^ (M + r) :=
        pow_dvd_pow π (by have := j.isLt; omega)
      have h2 : π ^ (r - (j : ℕ)) ∣ scaleVecN π y' j := ⟨y' j, rfl⟩
      have h3 := dvd_add (h1.trans (dvd_sub_comm.mp (hdvdb j))) h2
      rwa [sub_add_cancel] at h3
    choose f hf using hfac
    have hbf : b = scaleVecN π f := by
      funext j
      rw [hf j]
      rfl
    have hff : proj O r M f = proj O r M y' := by
      refine (proj_eq_iff_dvd hπ _ _).2 fun j => ?_
      have h1 : π ^ (M + r) ∣ scaleVecN π y' j - b j := hdvdb j
      rw [hbf] at h1
      have h2 : scaleVecN π y' j - scaleVecN π f j
          = π ^ (r - (j : ℕ)) * (y' j - f j) := by
        show π ^ (r - (j : ℕ)) * y' j - π ^ (r - (j : ℕ)) * f j = _
        ring
      rw [h2] at h1
      have h3 : π ^ (r - (j : ℕ)) * π ^ (M + (j : ℕ))
          ∣ π ^ (r - (j : ℕ)) * (y' j - f j) := by
        refine dvd_trans ?_ h1
        rw [← pow_add]
        exact pow_dvd_pow π (by have := j.isLt; omega)
      have h4 : π ^ (M + (j : ℕ)) ∣ y' j - f j :=
        (mul_dvd_mul_iff_left (pow_ne_zero _ hπ.ne_zero)).mp h3
      have h5 : π ^ M ∣ y' j - f j :=
        (pow_dvd_pow π (by omega)).trans h4
      exact h5
    have hτ : typeOf (monicPoly f) = τ := hy f (by rw [hff])
    rw [hbf]
    rw [typeOf_scaleVecN hπ f]
    exact hτ

/-- **THE UPPER TRANSPORT**: every scaling preimage of a census member is decided-`τ`
at the full window — `typeOf_scaleVecN` backwards. -/
private theorem trunc_decided_of_census {π : O} (hπ : Irreducible π) {h e' r M : ℕ}
    {τ : FactorizationType} {y : Coeff O r (M + r)}
    (hmem : scaledHom π (M + r) (fun j : Fin r => r - (j : ℕ)) y
      ∈ steepDecCensus O r (M + r) h e' τ) :
    y ∈ decidedSet O r τ (M + r) := by
  obtain ⟨y', rfl⟩ := proj_surjective O r (M + r) y
  have hΘ : scaledHom π (M + r) (fun j : Fin r => r - (j : ℕ)) (proj O r (M + r) y')
      = proj O r (M + r) (scaleVecN π y') := by
    funext t
    rw [scaledHom_apply]
    show Ideal.Quotient.mk ((maximalIdeal O) ^ (M + r)) (π ^ (r - (t : ℕ)))
        * Ideal.Quotient.mk ((maximalIdeal O) ^ (M + r)) (y' t)
      = Ideal.Quotient.mk ((maximalIdeal O) ^ (M + r)) (scaleVecN π y' t)
    rw [← map_mul]
    rfl
  rw [hΘ] at hmem
  intro s hs
  have hscale : proj O r (M + r) (scaleVecN π s) = proj O r (M + r) (scaleVecN π y') := by
    refine (proj_eq_iff_dvd hπ _ _).2 fun j => ?_
    have h1 := (proj_eq_iff_dvd hπ _ _).1 hs j
    have h2 : scaleVecN π y' j - scaleVecN π s j = π ^ (r - (j : ℕ)) * (y' j - s j) := by
      show π ^ (r - (j : ℕ)) * y' j - π ^ (r - (j : ℕ)) * s j = _
      ring
    rw [h2]
    exact Dvd.dvd.mul_left h1 _
  have hτs : typeOf (monicPoly (scaleVecN π s)) = τ := hmem.2 _ hscale
  have h3 := typeOf_scaleVecN hπ s
  rw [hτs] at h3
  exact h3.symm

/-- **THE SPECIAL COUNT SQUEEZE** (exact at every level):
`#dec(M)·q^{r·r} ≤ #census(M+r)·q^{bigT r} ≤ #dec(M+r)`. -/
private theorem card_census_special_bounds {π : O} (hπ : Irreducible π) {h e' r : ℕ}
    (hhe : h < e') (hr : 1 ≤ r) (hspec : r * (e' - h) ≤ e')
    (τ : FactorizationType) (M : ℕ) :
    decidedCount O r τ M * residueCard O ^ (r * r)
        ≤ Nat.card (steepDecCensus O r (M + r) h e' τ) * residueCard O ^ (bigTLoop r)
      ∧ Nat.card (steepDecCensus O r (M + r) h e' τ) * residueCard O ^ (bigTLoop r)
        ≤ decidedCount O r τ (M + r) := by
  classical
  have hκ : ∀ t : Fin r, (fun j : Fin r => r - (j : ℕ)) t ≤ M + r := fun t => by
    show r - (t : ℕ) ≤ M + r
    omega
  have hsub : steepDecCensus O r (M + r) h e' τ
      ⊆ Set.range (scaledHom π (M + r) (fun j : Fin r => r - (j : ℕ))) := by
    intro ρ hρ
    refine (mem_range_scaledHom hπ _ hκ ρ).mpr fun t => ?_
    exact special_box_read hhe hspec t.isLt (hρ.1 t)
  have hpre := card_preimage_of_subset_range
    (scaledHom π (M + r) (fun j : Fin r => r - (j : ℕ)))
    (steepDecCensus O r (M + r) h e' τ) hsub
  rw [card_ker_scaledHom hπ _ hκ, sum_fin_sub_eq_bigTLoop] at hpre
  constructor
  · -- LOWER: the truncation-decided cylinder scales into the census
    have hsubL : (coeffFactor r (by omega : M ≤ M + r)) ⁻¹' (decidedSet O r τ M)
        ⊆ (scaledHom π (M + r) (fun j : Fin r => r - (j : ℕ))) ⁻¹'
          (steepDecCensus O r (M + r) h e' τ) := by
      intro y hy
      exact census_of_trunc_decided hπ hhe hr hy
    have hcard1 : Nat.card ((coeffFactor r (by omega : M ≤ M + r)) ⁻¹'
          (decidedSet O r τ M) : Set (Coeff O r (M + r)))
        = decidedCount O r τ M * residueCard O ^ (r * (M + r - M)) :=
      card_preimage_coeffFactor_eq r (by omega) (decidedSet O r τ M)
    have hmono : Nat.card ((coeffFactor r (by omega : M ≤ M + r)) ⁻¹'
          (decidedSet O r τ M) : Set (Coeff O r (M + r)))
        ≤ Nat.card ((scaledHom π (M + r) (fun j : Fin r => r - (j : ℕ))) ⁻¹'
            (steepDecCensus O r (M + r) h e' τ) : Set (Coeff O r (M + r))) := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hsubL (Set.toFinite _)
    rw [hcard1, hpre] at hmono
    have hMM : r * (M + r - M) = r * r := by
      congr 1
      omega
    rw [hMM] at hmono
    have hcomm : residueCard O ^ (bigTLoop r)
        * Nat.card (steepDecCensus O r (M + r) h e' τ)
      = Nat.card (steepDecCensus O r (M + r) h e' τ)
        * residueCard O ^ (bigTLoop r) := Nat.mul_comm _ _
    omega
  · -- UPPER: the census's scaling preimage is decided at the full window
    have hsubU : (scaledHom π (M + r) (fun j : Fin r => r - (j : ℕ))) ⁻¹'
        (steepDecCensus O r (M + r) h e' τ) ⊆ decidedSet O r τ (M + r) := by
      intro y hy
      exact trunc_decided_of_census hπ hy
    have hmono : Nat.card ((scaledHom π (M + r) (fun j : Fin r => r - (j : ℕ))) ⁻¹'
          (steepDecCensus O r (M + r) h e' τ) : Set (Coeff O r (M + r)))
        ≤ Nat.card (decidedSet O r τ (M + r)) := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hsubU (Set.toFinite _)
    rw [hpre] at hmono
    have hdc : Nat.card (decidedSet O r τ (M + r)) = decidedCount O r τ (M + r) := rfl
    rw [hdc] at hmono
    have hcomm : residueCard O ^ (bigTLoop r)
        * Nat.card (steepDecCensus O r (M + r) h e' τ)
      = Nat.card (steepDecCensus O r (M + r) h e' τ)
        * residueCard O ^ (bigTLoop r) := Nat.mul_comm _ _
    omega

/-- ★★ **THE SPECIAL-FRAME CENSUS LAW**: at the frames with `r·(e' − h) ≤ e'` the
steep decided census law FOLLOWS from the mass-`r` value law — the strict cone is the
integer slope-1 box, the coordinate scaling preserves types in both directions, and
the census is squeezed between `decidedSeq(M)·q^{−bigT}` and
`decidedSeq(M+r)·q^{−bigT}`.  Value: `(n_τ/d_τ)(q)/q^{bigTLoop r}`. -/
theorem steepDecCensusLaw_of_special (r h e' : ℕ) (τ : FactorizationType)
    (hhe : h < e') (hr : 1 ≤ r) (hspec : r * (e' - h) ≤ e')
    (hvl : DecidedValueLaw r τ) :
    SteepDecCensusLaw r h e' τ := by
  obtain ⟨nτ, dτ, hd0, hval⟩ := hvl
  refine ⟨nτ, Polynomial.X ^ (bigTLoop r) * dτ,
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hd0, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hdO, hdens⟩ := hval O
  have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
  have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0 : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by omega)
  refine ⟨by
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    exact mul_ne_zero (pow_ne_zero _ hqQ) hdO, ?_⟩
  intro π hπ
  have hval2 : (((nτ.eval ((residueCard O : ℕ) : ℚ)
        / (Polynomial.X ^ (bigTLoop r) * dτ).eval ((residueCard O : ℕ) : ℚ)) : ℚ) : ℝ)
      = decidedDensity O r τ / ((residueCard O : ℕ) : ℝ) ^ (bigTLoop r) := by
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hdens]
    push_cast
    ring
  rw [hval2]
  have hlow : Filter.Tendsto (fun M : ℕ =>
      decidedSeq O r τ M / ((residueCard O : ℕ) : ℝ) ^ (bigTLoop r))
      Filter.atTop
      (nhds (decidedDensity O r τ / ((residueCard O : ℕ) : ℝ) ^ (bigTLoop r))) :=
    (decidedSeq_tendsto (O := O) r τ).div_const _
  have hupp : Filter.Tendsto (fun M : ℕ =>
      decidedSeq O r τ (M + r) / ((residueCard O : ℕ) : ℝ) ^ (bigTLoop r))
      Filter.atTop
      (nhds (decidedDensity O r τ / ((residueCard O : ℕ) : ℝ) ^ (bigTLoop r))) :=
    (((decidedSeq_tendsto (O := O) r τ).comp (tendsto_add_atTop_nat r))).div_const _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · refine Filter.Eventually.of_forall fun M => ?_
    have hb := (card_census_special_bounds hπ hhe hr hspec τ M).1
    have hR := (Nat.cast_le (α := ℝ)).mpr hb
    push_cast at hR
    show decidedSeq O r τ M / ((residueCard O : ℕ) : ℝ) ^ (bigTLoop r)
        ≤ (Nat.card (steepDecCensus O r (M + r) h e' τ) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (r * (M + r))
    have hseq : decidedSeq O r τ M
        = (decidedCount O r τ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (r * M) := rfl
    rw [hseq, div_div, ← pow_add,
      div_le_div_iff₀ (by positivity) (by positivity)]
    calc (decidedCount O r τ M : ℝ) * ((residueCard O : ℕ) : ℝ) ^ (r * (M + r))
        = (decidedCount O r τ M : ℝ) * ((residueCard O : ℕ) : ℝ) ^ (r * r)
          * ((residueCard O : ℕ) : ℝ) ^ (r * M) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          ring
      _ ≤ (Nat.card (steepDecCensus O r (M + r) h e' τ) : ℝ)
          * ((residueCard O : ℕ) : ℝ) ^ (bigTLoop r)
          * ((residueCard O : ℕ) : ℝ) ^ (r * M) := by
          exact mul_le_mul_of_nonneg_right hR (by positivity)
      _ = (Nat.card (steepDecCensus O r (M + r) h e' τ) : ℝ)
          * ((residueCard O : ℕ) : ℝ) ^ (r * M + bigTLoop r) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
  · refine Filter.Eventually.of_forall fun M => ?_
    have hb := (card_census_special_bounds hπ hhe hr hspec τ M).2
    have hR := (Nat.cast_le (α := ℝ)).mpr hb
    push_cast at hR
    show (Nat.card (steepDecCensus O r (M + r) h e' τ) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (r * (M + r))
        ≤ (decidedSeq O r τ ∘ fun M => M + r) M
          / ((residueCard O : ℕ) : ℝ) ^ (bigTLoop r)
    have hseq : (decidedSeq O r τ ∘ fun M => M + r) M
        = (decidedCount O r τ (M + r) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (r * (M + r)) := rfl
    rw [hseq, div_div, ← pow_add,
      div_le_div_iff₀ (by positivity) (by positivity)]
    calc (Nat.card (steepDecCensus O r (M + r) h e' τ) : ℝ)
          * ((residueCard O : ℕ) : ℝ) ^ (r * (M + r) + bigTLoop r)
        = (Nat.card (steepDecCensus O r (M + r) h e' τ) : ℝ)
          * ((residueCard O : ℕ) : ℝ) ^ (bigTLoop r)
          * ((residueCard O : ℕ) : ℝ) ^ (r * (M + r)) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          omega
      _ ≤ (decidedCount O r τ (M + r) : ℝ)
          * ((residueCard O : ℕ) : ℝ) ^ (r * (M + r)) := by
          exact mul_le_mul_of_nonneg_right hR (by positivity)

/-- ★★★ **THE SPECIAL-FRAME FIRE**: `SubfaceFrameLaw m h e' d σ` at every frame with
`r·(e' − h) ≤ e'` (`r := m − e'·d`), conditional on ONE smaller-mass value law
`DecidedValueLaw r τ` — the charge's item-3 shape, delivered on the special
subfamily (which includes r ≥ 2 frames, e.g. every `(h, e') = (e'−1, e')` with
`r ≤ e'`). -/
theorem subfaceFrameLaw_of_special (m h e' d r : ℕ) (σ : FactorizationType)
    (hh1 : 1 ≤ h) (hhe : h < e') (hcop : Nat.Coprime h e') (hd0 : 1 ≤ d) (hr : 1 ≤ r)
    (hm : m = e' * d + r) (hspec : r * (e' - h) ≤ e')
    (hvl : DecidedValueLaw r ⟨σ.data.erase (e', d)⟩) :
    SubfaceFrameLaw m h e' d σ :=
  subfaceFrameLaw_of_steepCensus m h e' d r σ hh1 hhe hcop hd0 hr hm
    (steepDecCensusLaw_of_special r h e' _ hhe hr hspec hvl)

/-- ★★★ **THE FIRST CLOSED r ≥ 2 FRAME LAW**: at `m = 6`, frame `(3, 4, 1)` — the
cofactor mass is `r = 2` and the frame is special (`2·(4 − 3) ≤ 4`), so the census
consumes the LANDED `DecidedSliceAt 2` (I02/I03w) and the sub-face frame law is
UNCONDITIONAL — the first machine-checked member of the family beyond SFW's r = 1
row. -/
theorem subfaceFrameLaw_r_two_witness :
    SubfaceFrameLaw 6 3 4 1 ⟨{(4, 1), (1, 1), (1, 1)}⟩ := by
  refine subfaceFrameLaw_of_special 6 3 4 1 2 _ (by omega) (by omega) (by decide)
    (by omega) (by omega) (by omega) (by omega) ?_
  show DecidedValueLaw 2 ⟨(({(4, 1), (1, 1), (1, 1)} : Multiset (ℕ × ℕ))).erase (4, 1)⟩
  have herase : (({(4, 1), (1, 1), (1, 1)} : Multiset (ℕ × ℕ))).erase (4, 1)
      = {(1, 1), (1, 1)} := by decide
  rw [herase]
  exact Uniformity.Density.decidedSliceAt_two ⟨{(1, 1), (1, 1)}⟩ (by decide)

end SpecialFire

end Uniformity.Density.IFCG72

end

/-! ## AXCHECK FOOTER — expected: `tSteep_le_iff`, `exact_factorization_unique`,
`fiber_eq_pairNbhd_gen`, and `mul_mem_subfaceCell_gen` are pure Lean core
`{propext, Classical.choice, Quot.sound}` (the fiber engine and the image never
consult the transport); everything consuming LSF's transport
(`subfaceCell_factors_gen`, `subfaceCell_gen_empty`, `subfaceFrameLaw_of_steepCensus`,
`subfaceFrameLaws_of_censusLaws`, the two census masters) is Lean core + EXACTLY the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42,
inherited through IFCG66/67/69 — never re-consumed); the capstone master additionally
inherits exactly `Uniformity.Density.Tower.agnprw_termination` (ID12's, previously
declared).  The C.33 cites, `AX_cellRecursion`, and `sorryAx` must NOT occur. -/

#print axioms Uniformity.Density.IFCG72.tSteep_le_iff
#print axioms Uniformity.Density.IFCG72.exact_factorization_unique
#print axioms Uniformity.Density.IFCG72.fiber_eq_pairNbhd_gen
#print axioms Uniformity.Density.IFCG72.mul_mem_subfaceCell_gen
#print axioms Uniformity.Density.IFCG72.subfaceCell_factors_gen
#print axioms Uniformity.Density.IFCG72.subfaceCell_gen_empty
#print axioms Uniformity.Density.IFCG72.subfaceFrameLaw_of_steepCensus
#print axioms Uniformity.Density.IFCG72.subfaceFrameLaws_of_censusLaws
#print axioms Uniformity.Density.IFCG72.decidedSliceAt_all_of_visCensus_census
#print axioms Uniformity.Density.IFCG72.decidedSliceAt_all_of_MASTER_CENSUS
#print axioms Uniformity.Density.IFCG72.capstoneHypotheses_of_MASTER_CENSUS
#print axioms Uniformity.Density.IFCG72.steepDecCensusLaw_one
#print axioms Uniformity.Density.IFCG72.steepDecCensusLaw_of_special
#print axioms Uniformity.Density.IFCG72.subfaceFrameLaw_of_special
#print axioms Uniformity.Density.IFCG72.subfaceFrameLaw_r_two_witness
