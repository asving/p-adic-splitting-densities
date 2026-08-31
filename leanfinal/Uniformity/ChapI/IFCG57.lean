/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG55

/-!
# Uniformity.ChapI.IFCG57 — UNIT LSC: the leaf-cell census — the general digit
bridge, the necklace count of the spanning leaf boxes, and the master's leaf row
re-based on the sub-face remainder

**UNIT LSC** (wave C, 2026-08-31).  RECUR (`IFCG35`) partitioned the ramified
remainder carrier into three recursion sectors and RIS (`IFCG37`) closed the leaf
sector's DECISIONS at every `(e', d)` (`decidedAt_of_spanning_irr`, Lean-core).  What
remained of `LeafSectorLaw e σ` — master premise 5 of IFCG55's
`decidedSliceAt_all_of_MASTER` — is THE COUNT.  This file lands it in the exact
partition form:

* **§1 the general digit polynomial.**  At face data `(h, e', d)` the residual
  positions of a class are `i = e'·k` (`k < d`) at levels `h·(d−k)`; `leafResPoly`
  is the monic degree-`d` polynomial over `ResidueField O` whose coefficients are
  those class digits (IFCG36's `resDig` instrument at general parameters).
* **§2 ★★ THE GENERAL DIGIT BRIDGE** (`classResidualPoly_eq_leafResPoly`): on the
  spanning height cone with exact corner, the CANONICAL class residual
  (`classResidualPoly`, IFCG35) IS the digit polynomial, pushed along B.59a's
  identification `resFieldXEquiv` — DBL's `e1_resPoly_eq` genre at arbitrary
  `(h, e', d)` (there: `(1, 2, 2)`).  Corollary: irreducibility of the class
  residual reads off the digits (`irreducible_classResidualPoly_iff`).
* **§3 ★★ THE NECKLACE COUNT** (`card_leafIrrBox`): the spanning leaf box at
  `(h, e', d)` has EXACTLY `N_d(q) · q^(mK − wLeaf h e' d)` classes at every finite
  level — the necklace census `N_d(q) = #IrredOfDeg(𝔽_q, d)` (IFCG19) over the digit
  fibers (the fiber engine at general parameters).  Cross-check: at
  `(h,e',d) = (1,2,2)` the weight is `wLeaf = 8` — DBL's landed
  `card_e1IrrBox_necklace = N₂(q)·q^(4K−8)` recovered exactly.
* **§4 ★★ THE SPANNING PARTITION.**  The leaf sector splits EXACTLY by whether the
  minimal face is attained at `0` (spanning: `e'·d = m`) or not (the sub-face
  cells).  The spanning part IS the union of the leaf boxes
  (`leafSpanSector_eq_biUnion`), is EMPTY unless `σ = ⟨{(e',d)}⟩` with `e'·d = m`,
  `d ≥ 2` (`d = 1` spanning is CN4's pure face, already outside the carrier), and
  its count is the exact monomial bank (`card_leafSpanSector`).
* **§5 ★★★ THE LAW RE-BASED.**  `zcURLim_leafSpanFam`: the spanning family has a
  uniform rational limit at EVERY `(m, σ)` — value `Σ_h N_d(q)/q^(wLeaf h e' d)` at
  the matching singleton type, `0` elsewhere — UNCONDITIONALLY.  The ONE named
  remaining Prop is `LeafSubfaceLaw m σ` (the non-spanning family's `ZcURLim`);
  `leafSectorLaw_of_subface` : sub-face law ⟹ `LeafSectorLaw m σ`.
* **§6 ★★★ THE MASTER RECOMPUTED** (`decidedSliceAt_all_of_MASTER'`,
  `capstoneHypotheses_of_MASTER'`): IFCG55's row 5 premise WEAKENS from the full
  `LeafSectorLaw` to the strictly smaller `LeafSubfaceLaw` — the spanning necklace
  census is machine-checked and leaves the premise surface.

## Honest scope

The non-spanning leaf cells are REAL (witness: `m = 5`, heights `(2,1,1,1,1)` — the
minimal face `[1,5]` of slope `1/4` has linear (irreducible) residual and the class
is decided `⟨{(1,1),(4,1)}⟩`), and their count couples the face digits to the
sub-face rest — the mass-`(m − e'd)` classes above the face line at the complementary
type — through a class-level two-block factorization correspondence that is NOT in
the corpus (IFCG38 recorded the same missing surjectivity leg for the split sector;
E2L flagged the genre as a full unit).  The charge's literal "fire `LeafSectorLaw`
via face boxes alone" is therefore mathematically unavailable; what is landed is the
exact partition, the closed spanning half, and the named remainder
`LeafSubfaceLaw` — nothing weakened, `LeafSectorLaw`'s statement byte-untouched.

## Axiom fence

§§1–5 (the bridge, the count, the partition identities, the spanning law, the
re-base) consume at most Lean core `{propext, Classical.choice, Quot.sound}` plus
the owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42) inherited through IFCG26/IFCG28's landed transports (the carrier's decided
sets) — never re-consumed.  §6 inherits IFCG55's fence (+ `agnprw_termination` on
the capstone wrapper only).  The C.33 cites must NOT occur.  Zero sorries at
landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG57

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFC7 (resOut mk_resOut)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG17 (decidedAt_unique)
open Uniformity.Density.IFCG19 (necklacePoly necklacePoly_eval_card)
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply classNPSupport_le le_classNPSupport)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq npHgt_monicPoly_top)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_sum shallowSet
  mem_stratum_X_pow_iff pureFaceSet faceBox faceH npHeight_coe card_setOf_le_resOrd
  card_pi_set)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG28 (onSide_monicPoly_iff sideSet_monicPoly_eq
  sideMin_monicPoly_eq sideMax_monicPoly_eq classSideSet)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_support minFaceAt_min
  minFaceAt_attained_lt minFaceAt_unique exists_minFaceAt_of_shallow
  classResidualPoly classResidualPoly_eq classResidualPoly_natDegree_pos
  leafSector leafSectorCount LeafSectorLaw remainderCarrier)
open Uniformity.Density.IFCG36 (resDig resDig_mk card_setOf_resDig
  resOrd_eq_iff_resDig)
open Uniformity.Density.IFCG37 (isKey_X xres resPoly_x_frame resCoeff_x_frame
  irreducible_resPoly_x_iff decidedAt_of_spanning_irr)
open Uniformity.Density.IFCG38 (SplitConvolutionDefectLaw)
open Uniformity.Density.IFCG44 (PowerConvolutionDefectLaw)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG51 (EisFullSpanRemainderLaw)

attribute [local instance] Classical.propDecidable

/-! ## §0 — the ceiling kit: the face thresholds and the leaf weight -/

section Kit

/-- The ceiling threshold `⌈h(m−i)/e'⌉` of the slope-`h/e'` face at abscissa `i`
(CN4's `tF` at general denominator). -/
def tLeaf (h e' m i : ℕ) : ℕ := (h * (m - i) + (e' - 1)) / e'

theorem tLeaf_le_iff {e' : ℕ} (he' : 0 < e') (h m i v : ℕ) :
    tLeaf h e' m i ≤ v ↔ h * (m - i) ≤ e' * v := by
  unfold tLeaf
  rw [Nat.div_le_iff_le_mul_add_pred he']
  omega

/-- At a residual position `i = e'·k` of the spanning face the threshold is EXACT:
`tLeaf = h·(d−k)`. -/
theorem tLeaf_mul {e' : ℕ} (he' : 0 < e') (h d k : ℕ) (hk : k ≤ d) :
    tLeaf h e' (e' * d) (e' * k) = h * (d - k) := by
  have hsub : e' * d - e' * k = e' * (d - k) := by
    have h1 : e' * (d - k) + e' * k = e' * d := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hk]
    omega
  unfold tLeaf
  rw [hsub]
  have h2 : h * (e' * (d - k)) = e' * (h * (d - k)) := by ring
  rw [h2, Nat.mul_add_div he']
  rw [Nat.div_eq_of_lt (by omega : e' - 1 < e'), Nat.add_zero]

/-- The corner threshold caps the whole face: `tLeaf ≤ h·d` at every abscissa. -/
theorem tLeaf_le_corner {e' : ℕ} (he' : 0 < e') (h d i : ℕ) :
    tLeaf h e' (e' * d) i ≤ h * d := by
  have h0 := tLeaf_mul he' h d 0 (Nat.zero_le d)
  rw [Nat.mul_zero, Nat.sub_zero] at h0
  calc tLeaf h e' (e' * d) i
      ≤ tLeaf h e' (e' * d) 0 := by
        unfold tLeaf
        exact Nat.div_le_div_right (Nat.add_le_add_right
          (Nat.mul_le_mul (le_refl h) (by omega)) _)
    _ = h * d := h0

/-- **The leaf weight** — the `K`-independent exponent of the `(h, e', d)` box:
one threshold per abscissa plus one digit pin per residual position. -/
def wLeaf (h e' d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (e' * d), (tLeaf h e' (e' * d) i + if e' ∣ i then 1 else 0)

end Kit

/-! ## §1 — the general digit polynomial at face data `(h, e', d)` -/

section DigitPoly

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The total coordinate read (junk `0` beyond the window). -/
def resAt {m K : ℕ} (c : Coeff O m K) (j : ℕ) : Res O K :=
  if hj : j < m then c ⟨j, hj⟩ else 0

theorem resAt_lt {m K : ℕ} (c : Coeff O m K) {j : ℕ} (hj : j < m) :
    resAt c j = c ⟨j, hj⟩ := dif_pos hj

/-- **The `k`-th residual digit** of the class at face data `(h, e', d)`: the digit of
coordinate `e'·k` at level `h·(d−k)` — the coefficient of the side residual
(the bridge, §2). -/
def leafDig (π : O) {m K : ℕ} (h e' d : ℕ) (c : Coeff O m K) (k : ℕ) :
    ResidueField O :=
  resDig π (h * (d - k)) (resAt c (e' * k))

/-- **The general digit polynomial**: monic of degree `d`, lower coefficients the
residual digits. -/
def leafResPoly (π : O) {m K : ℕ} (h e' d : ℕ) (c : Coeff O m K) :
    Polynomial (ResidueField O) :=
  Polynomial.X ^ d
    + ∑ k ∈ Finset.range d, Polynomial.C (leafDig π h e' d c k) * Polynomial.X ^ k

theorem leafResPoly_coeff_lt (π : O) {m K : ℕ} (h e' d : ℕ) (c : Coeff O m K)
    {k : ℕ} (hk : k < d) :
    (leafResPoly π h e' d c).coeff k = leafDig π h e' d c k := by
  unfold leafResPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega : ¬ k = d),
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range d) k (fun j => leafDig π h e' d c j),
    if_pos (Finset.mem_range.mpr hk), zero_add]

theorem leafResPoly_coeff_top (π : O) {m K : ℕ} (h e' d : ℕ) (c : Coeff O m K) :
    (leafResPoly π h e' d c).coeff d = 1 := by
  unfold leafResPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl,
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range d) d (fun j => leafDig π h e' d c j),
    if_neg (by simp), add_zero]

theorem leafResPoly_coeff_gt (π : O) {m K : ℕ} (h e' d : ℕ) (c : Coeff O m K)
    {k : ℕ} (hk : d < k) :
    (leafResPoly π h e' d c).coeff k = 0 := by
  unfold leafResPoly
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg (by omega : ¬ k = d),
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range d) k (fun j => leafDig π h e' d c j),
    if_neg (by rw [Finset.mem_range]; omega), zero_add]

theorem leafResPoly_natDegree (π : O) {m K : ℕ} (h e' d : ℕ) (c : Coeff O m K) :
    (leafResPoly π h e' d c).natDegree = d := by
  have hle : (leafResPoly π h e' d c).natDegree ≤ d :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk =>
      leafResPoly_coeff_gt π h e' d c hk
  have hge : d ≤ (leafResPoly π h e' d c).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by
      rw [leafResPoly_coeff_top]; exact one_ne_zero)
  omega

theorem leafResPoly_monic (π : O) {m K : ℕ} (h e' d : ℕ) (c : Coeff O m K) :
    (leafResPoly π h e' d c).Monic := by
  show (leafResPoly π h e' d c).coeff (leafResPoly π h e' d c).natDegree = 1
  rw [leafResPoly_natDegree, leafResPoly_coeff_top]

/-- **Reconstruction**: the digit polynomial equals a given monic degree-`d`
polynomial iff the digits match its lower coefficients. -/
theorem leafResPoly_eq_iff (π : O) {m K : ℕ} (h e' d : ℕ) (c : Coeff O m K)
    {f : Polynomial (ResidueField O)} (hf : f.Monic) (hfd : f.natDegree = d) :
    leafResPoly π h e' d c = f ↔ ∀ k, k < d → leafDig π h e' d c k = f.coeff k := by
  constructor
  · intro he k hk
    rw [← leafResPoly_coeff_lt π h e' d c hk, he]
  · intro hall
    have hsum := hf.as_sum
    rw [hfd] at hsum
    rw [hsum]
    unfold leafResPoly
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hall k (Finset.mem_range.mp hk)]

/-- Over any field, an irreducible polynomial of degree `≥ 2` has nonzero constant
term (else `X` divides it). -/
theorem coeff_zero_ne_zero_of_irreducible {F : Type*} [Field F] {p : Polynomial F}
    (hirr : Irreducible p) (hdeg : 2 ≤ p.natDegree) : p.coeff 0 ≠ 0 := by
  intro h0
  obtain ⟨g, hg⟩ := Polynomial.X_dvd_iff.mpr h0
  have hg0 : g ≠ 0 := by
    intro hgz
    rw [hgz, mul_zero] at hg
    rw [hg] at hdeg
    simp at hdeg
  rcases hirr.isUnit_or_isUnit hg with hu | hu
  · exact Polynomial.not_isUnit_X hu
  · have hdg := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [hg, Polynomial.natDegree_mul Polynomial.X_ne_zero hg0,
      Polynomial.natDegree_X, hdg] at hdeg
    omega

end DigitPoly

/-! ## §2 — ★★ THE GENERAL DIGIT BRIDGE -/

section Bridge

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The spanning height cone at `(h, e')`**: the whole class polygon on or above
the line through `(m, 0)` of slope `h/e'` — CN4's `faceBox` genre at general
denominator, corner NOT pinned. -/
def leafCone (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m K h e' : ℕ) : Set (Coeff O m K) :=
  {c | ∀ i : Fin m, h * (m - (i : ℕ)) ≤ e' * resOrd (c i)}

/-- **The spanning leaf box at `(h, e', d)`**: the height cone with IRREDUCIBLE digit
polynomial — the residual-irreducible spanning cells (§4). -/
def leafIrrBox (π : O) (m K h e' d : ℕ) : Set (Coeff O m K) :=
  {c | c ∈ leafCone O m K h e' ∧ Irreducible (leafResPoly π h e' d c)}

/-- `classSideSet` membership, unfolded through the Classical filter (the B83Kit
idiom, private copy). -/
private theorem mem_classSideSet_iff {m K : ℕ} {c : Coeff O m K} {u ℓ j : ℕ} :
    j ∈ classSideSet c u ℓ ↔ (j < m + 1 ∧ NPAttains c u ℓ j) := by
  classical
  constructor
  · intro hj
    have hj' : j ∈ Finset.filter (NPAttains c u ℓ) (Finset.range (m + 1)) := hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj'
    exact ⟨Finset.mem_range.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hj' : j ∈ Finset.filter (NPAttains c u ℓ) (Finset.range (m + 1)) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩
    exact hj'

/-- On the cone with exact corner, the class support is `h·m`, attained at `0` and
at the monic point — the spanning face, class-level. -/
theorem leafCone_face_data {h e' d m K : ℕ} (hh : 0 < h) (hhe : h < e')
    (_hd0 : 0 < d) (hm : m = e' * d) (hm0 : 0 < m) (hmK : m ≤ K) {c : Coeff O m K}
    (hbox : ∀ i : Fin m, h * (m - (i : ℕ)) ≤ e' * resOrd (c i))
    (hv0 : resOrd (c ⟨0, hm0⟩) = h * d) :
    classNPSupport c h e' = h * m ∧ NPAttains c h e' 0 ∧ NPAttains c h e' m
      ∧ NPVisibleAt c h e' := by
  have he'0 : 0 < e' := by omega
  have hnpm : npHeight c m = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl m)]
  have hsup : classNPSupport c h e' = h * m := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h2 := classNPSupport_le_apply c h e' (le_refl m)
      rw [hnpm] at h2
      omega
    · intro i hi
      rcases eq_or_lt_of_le hi with heq | hilt
      · subst heq
        rw [hnpm]
        omega
      · have hf : h * (m - i) ≤ e' * resOrd (c ⟨i, hilt⟩) := hbox ⟨i, hilt⟩
        have hnp : npHeight c i = resOrd (c ⟨i, hilt⟩) := by
          have h5 := npHeight_coe c ⟨i, hilt⟩
          simpa using h5
        rw [hnp]
        have hdist : h * (m - i) + h * i = h * m := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hilt)]
        omega
  have hnp0 : npHeight c 0 = resOrd (c ⟨0, hm0⟩) := by
    have h5 := npHeight_coe c ⟨0, hm0⟩
    simpa using h5
  have hA0 : NPAttains c h e' 0 := by
    refine ⟨Nat.zero_le m, ?_⟩
    rw [hnp0, hv0, hsup, hm]
    ring
  have hAm : NPAttains c h e' m := by
    refine ⟨le_refl m, ?_⟩
    rw [hnpm, hsup]
    ring
  have hvis : NPVisibleAt c h e' := by
    show classNPSupport c h e' < e' * K
    rw [hsup]
    have h1 : h + 1 ≤ e' := hhe
    have h2 := Nat.mul_le_mul h1 (le_refl m)
    have h3 : h * m + m = (h + 1) * m := by ring
    have h4 : e' * m ≤ e' * K := Nat.mul_le_mul (le_refl e') hmK
    have h5 : e' * m = m * e' := Nat.mul_comm e' m
    have h6 : (h + 1) * m = m * (h + 1) := Nat.mul_comm _ _
    omega
  exact ⟨hsup, hA0, hAm, hvis⟩

variable [IsAdicComplete (maximalIdeal O) O]

/-- ★★ **THE GENERAL DIGIT BRIDGE** (DBL's `e1_resPoly_eq` at arbitrary
`(h, e', d)`): on the spanning height cone with exact corner `v₀ = h·d`, the
canonical class residual at the minimal face IS the digit polynomial, pushed along
B.59a's identification of the x-frame residual field with the residue field. -/
theorem classResidualPoly_eq_leafResPoly {π : O} (hπ : Irreducible π)
    {h e' d : ℕ} (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d)
    {m K : ℕ} (hm : m = e' * d) (hm0 : 0 < m) (hmK : m ≤ K) {c : Coeff O m K}
    (hbox : ∀ i : Fin m, h * (m - (i : ℕ)) ≤ e' * resOrd (c i))
    (hv0 : resOrd (c ⟨0, hm0⟩) = h * d) :
    classResidualPoly π c h e'
      = (leafResPoly π h e' d c).map
          (resFieldXEquiv O : IsLocalRing.ResidueField O →+* resField (X : Polynomial O)) := by
  have he'0 : 0 < e' := by omega
  have hhd : h * d < m := by
    rw [hm]
    have h1 : h + 1 ≤ e' := hhe
    have h2 := Nat.mul_le_mul h1 (le_refl d)
    have h3 : h * d + d = (h + 1) * d := by ring
    omega
  obtain ⟨hsup, hA0, hAm, hvis⟩ :=
    leafCone_face_data hh hhe hd0 hm hm0 hmK hbox hv0
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  -- the lift's side data: the side set is the class attainment set, spanning [0, m]
  have h0mem : (0 : ℕ) ∈ classSideSet c h e' :=
    mem_classSideSet_iff.mpr ⟨by omega, hA0⟩
  have hmmem : m ∈ classSideSet c h e' :=
    mem_classSideSet_iff.mpr ⟨by omega, hAm⟩
  have hcne : (classSideSet c h e').Nonempty := ⟨0, h0mem⟩
  have hne : (sideSet X (monicPoly a) h e').Nonempty := by
    rw [sideSet_monicPoly_eq hπ he'0 hvis ha]
    exact hcne
  have hmin0 : sideMin X (monicPoly a) h e' hne = 0 := by
    have h1 := sideMin_monicPoly_eq hπ he'0 hvis ha hne hcne
    have h2 : (classSideSet c h e').min' hcne ≤ 0 := Finset.min'_le _ 0 h0mem
    omega
  have hmaxm : sideMax X (monicPoly a) h e' hne = m := by
    have h1 := sideMax_monicPoly_eq hπ he'0 hvis ha hne hcne
    have h2 : (classSideSet c h e').max' hcne = m := by
      refine le_antisymm ?_ (Finset.le_max' _ m hmmem)
      have h3 := Finset.max'_mem (classSideSet c h e') hcne
      obtain ⟨h4, -⟩ := mem_classSideSet_iff.mp h3
      omega
    rw [h1, h2]
  -- the left height is the exact corner
  have hcv : classCoeffVal c ⟨0, hm0⟩ = h * d := hv0
  have hlt : classCoeffVal c ⟨0, hm0⟩ < K := by
    rw [hcv]
    omega
  have hH : npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne)
      = ((h * d : ℕ) : ℕ∞) := by
    rw [hmin0]
    have h1 := npHgt_monicPoly_eq hπ ha hm0 hlt
    rw [h1, hcv]
  -- the canonical residual is the lift's residual, is the x-frame digit polynomial
  have hcrp := classResidualPoly_eq hπ he'0 hvis ha hne hH
  rw [hcrp, resPoly_x_frame]
  congr 1
  -- the x-frame digit polynomial IS the leaf digit polynomial
  have hsdeg : sideDeg X (monicPoly a) h e' hne = d := by
    unfold sideDeg
    rw [hmaxm, hmin0, Nat.sub_zero, hm, Nat.mul_div_cancel_left d he'0]
  unfold xres leafResPoly
  rw [hsdeg, hmin0, Finset.sum_range_succ]
  have htop : Polynomial.C (digAt π (h * d - h * d) ((monicPoly a).coeff (0 + e' * d)))
      * Polynomial.X ^ d = (Polynomial.X : Polynomial (IsLocalRing.ResidueField O)) ^ d := by
    have h1 : (monicPoly a).coeff (0 + e' * d) = 1 := by
      rw [Nat.zero_add, ← hm]
      have h2 := (monicPoly_monic a).coeff_natDegree
      rwa [monicPoly_natDegree] at h2
    rw [h1, Nat.sub_self]
    have h3 : digAt π 0 (1 : O) = 1 := by
      have h4 : (1 : O) = π ^ 0 * 1 := by rw [pow_zero, one_mul]
      rw [digAt_eq hπ h4, map_one]
    rw [h3, map_one, one_mul]
  have hSum : (∑ k ∈ Finset.range d,
        Polynomial.C (digAt π (h * d - h * k) ((monicPoly a).coeff (0 + e' * k)))
          * Polynomial.X ^ k)
      = ∑ k ∈ Finset.range d,
          Polynomial.C (leafDig π h e' d c k) * Polynomial.X ^ k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkd : k < d := Finset.mem_range.mp hk
    have hklt : e' * k < m := by
      rw [hm]
      have h1 := Nat.mul_le_mul (le_refl e') (show k + 1 ≤ d by omega)
      have h2 : e' * k + e' = e' * (k + 1) := by ring
      omega
    have hcoeff : (monicPoly a).coeff (0 + e' * k) = a ⟨e' * k, hklt⟩ := by
      rw [Nat.zero_add]
      exact monicPoly_coeff_lt a hklt
    have hlev : h * d - h * k = h * (d - k) := by
      have h1 : h * (d - k) + h * k = h * d := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hkd)]
      omega
    have hlevK : h * (d - k) < K := by
      have h1 : h * (d - k) ≤ h * d := Nat.mul_le_mul (le_refl h) (Nat.sub_le d k)
      omega
    congr 1
    rw [hcoeff, hlev]
    unfold leafDig
    rw [resAt_lt c hklt]
    have hc : c ⟨e' * k, hklt⟩
        = Ideal.Quotient.mk ((maximalIdeal O) ^ K) (a ⟨e' * k, hklt⟩) := by
      rw [← ha]
      rfl
    rw [hc, resDig_mk hπ hlevK]
  rw [htop, hSum, add_comm]

/-- ★ Irreducibility of the class residual reads off the digit polynomial
(the genre transport, IFCG37's `irreducible_resPoly_x_iff` idiom). -/
theorem irreducible_classResidualPoly_iff {π : O} (hπ : Irreducible π)
    {h e' d : ℕ} (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d)
    {m K : ℕ} (hm : m = e' * d) (hm0 : 0 < m) (hmK : m ≤ K) {c : Coeff O m K}
    (hbox : ∀ i : Fin m, h * (m - (i : ℕ)) ≤ e' * resOrd (c i))
    (hv0 : resOrd (c ⟨0, hm0⟩) = h * d) :
    Irreducible (classResidualPoly π c h e')
      ↔ Irreducible (leafResPoly π h e' d c) := by
  rw [classResidualPoly_eq_leafResPoly hπ hh hhe hd0 hm hm0 hmK hbox hv0]
  have hmap : (leafResPoly π h e' d c).map
        (resFieldXEquiv O : IsLocalRing.ResidueField O →+* resField (X : Polynomial O))
      = Polynomial.mapEquiv (resFieldXEquiv O) (leafResPoly π h e' d c) := rfl
  rw [hmap]
  exact MulEquiv.irreducible_iff (Polynomial.mapEquiv (resFieldXEquiv O))

end Bridge

/-! ## §3 — ★★ THE NECKLACE COUNT of the spanning leaf box -/

section Count

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Counting bridge (IFCG24's private helper, reproduced). -/
private theorem natCard_set_eq_card_filter {γ : Type*} [Fintype γ] (s : Set γ) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

/-- The fibre-partition helper (IFCG24's private helper, reproduced). -/
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

/-- **The digit fiber at a genre polynomial `f`**: thresholds everywhere, digits
pinned to `f`'s coefficients at the residual positions. -/
def leafFiber (π : O) (m K h e' d : ℕ) (f : Polynomial (IsLocalRing.ResidueField O)) :
    Set (Coeff O m K) :=
  {c | ∀ i : Fin m, c i ∈
    (if e' ∣ (i : ℕ)
     then {x : Res O K | h * (d - (i : ℕ) / e') ≤ resOrd x
            ∧ resDig π (h * (d - (i : ℕ) / e')) x = f.coeff ((i : ℕ) / e')}
     else {x : Res O K | tLeaf h e' m (i : ℕ) ≤ resOrd x})}

/-- Fiber membership = cone membership + the digit-polynomial pin. -/
theorem mem_leafFiber_iff {π : O} (_hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') {m K : ℕ} (hm : m = e' * d) (hmK : m ≤ K)
    {f : Polynomial (IsLocalRing.ResidueField O)} (hfm : f.Monic) (hfd : f.natDegree = d)
    (c : Coeff O m K) :
    c ∈ leafFiber π m K h e' d f
      ↔ c ∈ leafCone O m K h e' ∧ leafResPoly π h e' d c = f := by
  subst hm
  have he'0 : 0 < e' := by omega
  constructor
  · intro hc
    have hcone : c ∈ leafCone O (e' * d) K h e' := by
      intro i
      by_cases hdvd : e' ∣ (i : ℕ)
      · have hci := hc i
        rw [if_pos hdvd] at hci
        have hk : (i : ℕ) / e' < d := by
          rw [Nat.div_lt_iff_lt_mul he'0]
          have h1 := i.isLt
          have h2 : d * e' = e' * d := Nat.mul_comm d e'
          omega
        have hteq : tLeaf h e' (e' * d) (i : ℕ) = h * (d - (i : ℕ) / e') := by
          conv_lhs => rw [← Nat.mul_div_cancel' hdvd]
          exact tLeaf_mul he'0 h d ((i : ℕ) / e') (le_of_lt hk)
        have h3 : tLeaf h e' (e' * d) (i : ℕ) ≤ resOrd (c i) := by
          rw [hteq]
          exact hci.1
        exact (tLeaf_le_iff he'0 h (e' * d) (i : ℕ) _).mp h3
      · have hci := hc i
        rw [if_neg hdvd] at hci
        exact (tLeaf_le_iff he'0 h (e' * d) (i : ℕ) _).mp hci
    refine ⟨hcone, ?_⟩
    rw [leafResPoly_eq_iff π h e' d c hfm hfd]
    intro k hk
    have hklt : e' * k < e' * d := by
      have h1 := Nat.mul_le_mul (le_refl e') (show k + 1 ≤ d by omega)
      have h2 : e' * k + e' = e' * (k + 1) := by ring
      omega
    have hci := hc ⟨e' * k, hklt⟩
    have hdvd : e' ∣ ((⟨e' * k, hklt⟩ : Fin (e' * d)) : ℕ) := Dvd.intro k rfl
    rw [if_pos hdvd] at hci
    have hdiv : ((⟨e' * k, hklt⟩ : Fin (e' * d)) : ℕ) / e' = k := by
      show e' * k / e' = k
      exact Nat.mul_div_cancel_left k he'0
    rw [hdiv] at hci
    unfold leafDig
    rw [resAt_lt c hklt]
    exact hci.2
  · rintro ⟨hcone, hpin⟩
    intro i
    by_cases hdvd : e' ∣ (i : ℕ)
    · rw [if_pos hdvd]
      have hk : (i : ℕ) / e' < d := by
        rw [Nat.div_lt_iff_lt_mul he'0]
        have h1 := i.isLt
        have h2 : d * e' = e' * d := Nat.mul_comm d e'
        omega
      have hteq : tLeaf h e' (e' * d) (i : ℕ) = h * (d - (i : ℕ) / e') := by
        conv_lhs => rw [← Nat.mul_div_cancel' hdvd]
        exact tLeaf_mul he'0 h d ((i : ℕ) / e') (le_of_lt hk)
      refine ⟨?_, ?_⟩
      · rw [← hteq]
        exact (tLeaf_le_iff he'0 h (e' * d) (i : ℕ) _).mpr (hcone i)
      · have hdig := (leafResPoly_eq_iff π h e' d c hfm hfd).mp hpin
          ((i : ℕ) / e') hk
        have hieq : e' * ((i : ℕ) / e') = (i : ℕ) := Nat.mul_div_cancel' hdvd
        have hilt : e' * ((i : ℕ) / e') < e' * d := by
          rw [hieq]
          exact i.isLt
        unfold leafDig at hdig
        rw [resAt_lt c hilt] at hdig
        have hfin : (⟨e' * ((i : ℕ) / e'), hilt⟩ : Fin (e' * d)) = i :=
          Fin.ext hieq
        rw [hfin] at hdig
        exact hdig
    · rw [if_neg hdvd]
      exact (tLeaf_le_iff he'0 h (e' * d) (i : ℕ) _).mpr (hcone i)

/-- ★ **The fiber count**: `q^(mK − wLeaf)` classes per genre polynomial —
independent of `f`. -/
theorem card_leafFiber {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) {m K : ℕ} (hm : m = e' * d)
    (hmK : m ≤ K) (f : Polynomial (IsLocalRing.ResidueField O)) :
    Nat.card (leafFiber π m K h e' d f : Set (Coeff O m K))
      = residueCard O ^ (m * K - wLeaf h e' d) := by
  classical
  subst hm
  have he'0 : 0 < e' := by omega
  have hhd : h * d < e' * d := by
    have h1 : h + 1 ≤ e' := hhe
    have h2 := Nat.mul_le_mul h1 (le_refl d)
    have h3 : h * d + d = (h + 1) * d := by ring
    omega
  have hbound : ∀ i : ℕ,
      tLeaf h e' (e' * d) i + (if e' ∣ i then 1 else 0) ≤ K := by
    intro i
    have h1 := tLeaf_le_corner he'0 h d i
    by_cases hdvd : e' ∣ i
    · rw [if_pos hdvd]
      omega
    · rw [if_neg hdvd]
      omega
  unfold leafFiber
  rw [card_pi_set]
  have hfac : ∀ i : Fin (e' * d),
      Nat.card ((if e' ∣ (i : ℕ)
          then {x : Res O K | h * (d - (i : ℕ) / e') ≤ resOrd x
                ∧ resDig π (h * (d - (i : ℕ) / e')) x = f.coeff ((i : ℕ) / e')}
          else {x : Res O K | tLeaf h e' (e' * d) (i : ℕ) ≤ resOrd x}) : Set (Res O K))
        = residueCard O
            ^ (K - (tLeaf h e' (e' * d) (i : ℕ) + if e' ∣ (i : ℕ) then 1 else 0)) := by
    intro i
    by_cases hdvd : e' ∣ (i : ℕ)
    · rw [if_pos hdvd, if_pos hdvd]
      have hk : (i : ℕ) / e' < d := by
        rw [Nat.div_lt_iff_lt_mul he'0]
        have h1 := i.isLt
        have h2 : d * e' = e' * d := Nat.mul_comm d e'
        omega
      have hteq : tLeaf h e' (e' * d) (i : ℕ) = h * (d - (i : ℕ) / e') := by
        conv_lhs => rw [← Nat.mul_div_cancel' hdvd]
        exact tLeaf_mul he'0 h d ((i : ℕ) / e') (le_of_lt hk)
      have hlev : h * (d - (i : ℕ) / e') < K := by
        have h1 : h * (d - (i : ℕ) / e') ≤ h * d :=
          Nat.mul_le_mul (le_refl h) (Nat.sub_le d _)
        omega
      rw [card_setOf_resDig hπ hlev (f.coeff ((i : ℕ) / e'))]
      congr 1
      rw [hteq]
    · rw [if_neg hdvd, if_neg hdvd]
      have h1 := hbound (i : ℕ)
      rw [if_neg hdvd] at h1
      rw [card_setOf_le_resOrd (by omega : tLeaf h e' (e' * d) (i : ℕ) ≤ K)]
      congr 1
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun i => K - (tLeaf h e' (e' * d) i + if e' ∣ i then 1 else 0)) (e' * d)]
  have hsplit : (∑ i ∈ Finset.range (e' * d),
        (K - (tLeaf h e' (e' * d) i + if e' ∣ i then 1 else 0)))
      + (∑ i ∈ Finset.range (e' * d),
          (tLeaf h e' (e' * d) i + if e' ∣ i then 1 else 0)) = (e' * d) * K := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hbound i)),
      Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hw : wLeaf h e' d = ∑ i ∈ Finset.range (e' * d),
      (tLeaf h e' (e' * d) i + if e' ∣ i then 1 else 0) := rfl
  omega

/-- The genre carrier as a set (IFCG4's `IrredOfDeg`, set form). -/
def leafGenre (F : Type*) [Field F] (d : ℕ) : Set (Polynomial F) :=
  {f | f.Monic ∧ f.natDegree = d ∧ Irreducible f}

theorem finite_leafGenre (F : Type*) [Field F] [Fintype F] (d : ℕ) :
    (leafGenre F d).Finite := by
  haveI : Finite ↥(leafGenre F d) :=
    inferInstanceAs (Finite (Uniformity.Density.IFCG4.IrredOfDeg F d))
  exact Set.toFinite _

/-- ★★ **THE NECKLACE COUNT** (DBL's `card_e1IrrBox_necklace` at arbitrary
`(h, e', d)`): the spanning leaf box carries exactly `N_d(q) · q^(mK − wLeaf)`
classes at every finite level — the monic-irreducible census over the digit
fibers. -/
theorem card_leafIrrBox {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) {m K : ℕ} (hm : m = e' * d)
    (hmK : m ≤ K) :
    Nat.card (leafIrrBox π m K h e' d : Set (Coeff O m K))
      = Nat.card (Uniformity.Density.IFCG4.IrredOfDeg (IsLocalRing.ResidueField O) d)
          * residueCard O ^ (m * K - wLeaf h e' d) := by
  classical
  letI : Fintype (Coeff O m K) := Fintype.ofFinite _
  letI : Fintype (IsLocalRing.ResidueField O) := Fintype.ofFinite _
  have hfin : (leafGenre (IsLocalRing.ResidueField O) d).Finite := finite_leafGenre _ d
  rw [natCard_eq_sum_fiber (leafIrrBox π m K h e' d)
      (fun c => leafResPoly π h e' d c) hfin.toFinset
      (fun c hc => by
        rw [Set.Finite.mem_toFinset]
        exact ⟨leafResPoly_monic π h e' d c, leafResPoly_natDegree π h e' d c, hc.2⟩)]
  have hfib : ∀ f ∈ hfin.toFinset,
      Nat.card ((leafIrrBox π m K h e' d
          ∩ (fun c => leafResPoly π h e' d c) ⁻¹' {f}) : Set (Coeff O m K))
        = residueCard O ^ (m * K - wLeaf h e' d) := by
    intro f hf
    rw [Set.Finite.mem_toFinset] at hf
    obtain ⟨hfm, hfd, hfirr⟩ := hf
    have hset : leafIrrBox π m K h e' d
        ∩ (fun c => leafResPoly π h e' d c) ⁻¹' {f}
        = leafFiber π m K h e' d f := by
      ext c
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      rw [mem_leafFiber_iff hπ hh hhe hm hmK hfm hfd]
      constructor
      · rintro ⟨⟨hcone, -⟩, hpin⟩
        exact ⟨hcone, hpin⟩
      · rintro ⟨hcone, hpin⟩
        exact ⟨⟨hcone, by rw [hpin]; exact hfirr⟩, hpin⟩
    rw [hset, card_leafFiber hπ hh hhe hd0 hm hmK f]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  congr 1
  have h1 : hfin.toFinset.card
      = Nat.card ↥(leafGenre (IsLocalRing.ResidueField O) d) := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  rw [h1]
  rfl

/-- ★ **The corner is exact on the irreducible box** (`d ≥ 2`): the digit
polynomial's constant term is nonzero, so `v₀ = h·d` — the face is ATTAINED at
`0`. -/
theorem leafIrrBox_corner {π : O} (hπ : Irreducible π) {h e' d : ℕ}
    (hh : 0 < h) (hhe : h < e') (hd2 : 2 ≤ d) {m K : ℕ} (hm : m = e' * d)
    (hm0 : 0 < m) (hmK : m ≤ K) {c : Coeff O m K}
    (hc : c ∈ leafIrrBox π m K h e' d) :
    resOrd (c ⟨0, hm0⟩) = h * d := by
  obtain ⟨hcone, hirr⟩ := hc
  have he'0 : 0 < e' := by omega
  have hhd : h * d < m := by
    rw [hm]
    have h1 : h + 1 ≤ e' := hhe
    have h2 := Nat.mul_le_mul h1 (le_refl d)
    have h3 : h * d + d = (h + 1) * d := by ring
    omega
  have hge : h * d ≤ resOrd (c ⟨0, hm0⟩) := by
    have h1 : h * (m - ((⟨0, hm0⟩ : Fin m) : ℕ)) ≤ e' * resOrd (c ⟨0, hm0⟩) :=
      hcone ⟨0, hm0⟩
    have h2 : h * m ≤ e' * resOrd (c ⟨0, hm0⟩) := by
      simpa using h1
    have h3 : h * m = e' * (h * d) := by
      rw [hm]
      ring
    rw [h3] at h2
    exact Nat.le_of_mul_le_mul_left h2 he'0
  have hne : resDig π (h * d) (c ⟨0, hm0⟩) ≠ 0 := by
    have h0 := coeff_zero_ne_zero_of_irreducible hirr
      (by rw [leafResPoly_natDegree]; omega)
    rw [leafResPoly_coeff_lt π h e' d c (by omega : 0 < d)] at h0
    unfold leafDig at h0
    rw [Nat.mul_zero, resAt_lt c hm0, Nat.sub_zero] at h0
    exact h0
  exact (resOrd_eq_iff_resDig hπ (by omega : h * d < K) (c ⟨0, hm0⟩)).mpr ⟨hge, hne⟩

end Count

/-! ## §4 — ★★ the spanning partition of the leaf sector -/

section Partition

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The SPANNING leaf cells**: minimal face attained at `0` (the face covers
`[0, m]`, so `e'·d = m` and RIS's spanning decision applies). -/
def leafSpanSector (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (Coeff O m (M + m)) :=
  {c | c ∈ remainderCarrier O m σ M ∧ ∃ h e' : ℕ, MinFaceAt c h e'
    ∧ Irreducible (classResidualPoly π c h e') ∧ NPAttains c h e' 0}

/-- **The SUB-FACE leaf cells**: minimal face NOT attained at `0` — the carrier of
the named remainder (`LeafSubfaceLaw`). -/
def leafSubSector (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (Coeff O m (M + m)) :=
  {c | c ∈ remainderCarrier O m σ M ∧ ∃ h e' : ℕ, MinFaceAt c h e'
    ∧ Irreducible (classResidualPoly π c h e') ∧ ¬ NPAttains c h e' 0}

def leafSpanCount (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  Nat.card (leafSpanSector O π m σ M)

def leafSubCount (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  Nat.card (leafSubSector O π m σ M)

/-- The leaf sector is the union of the two halves (the minimal face either is or is
not attained at `0`). -/
theorem leafSector_eq_span_union_sub (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    leafSector O π m σ M = leafSpanSector O π m σ M ∪ leafSubSector O π m σ M := by
  ext c
  constructor
  · rintro ⟨hcar, h, e', hF, hirr⟩
    by_cases hA : NPAttains c h e' 0
    · exact Or.inl ⟨hcar, h, e', hF, hirr, hA⟩
    · exact Or.inr ⟨hcar, h, e', hF, hirr, hA⟩
  · rintro (⟨hcar, h, e', hF, hirr, -⟩ | ⟨hcar, h, e', hF, hirr, -⟩) <;>
      exact ⟨hcar, h, e', hF, hirr⟩

/-- The two halves are disjoint (the minimal face is unique). -/
theorem leafSpan_disjoint_sub (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Disjoint (leafSpanSector O π m σ M) (leafSubSector O π m σ M) := by
  rw [Set.disjoint_left]
  rintro c ⟨-, h₁, e₁, hF₁, -, hA₁⟩ ⟨-, h₂, e₂, hF₂, -, hnA₂⟩
  obtain ⟨hh, he⟩ := minFaceAt_unique hF₁ hF₂
  subst hh
  subst he
  exact hnA₂ hA₁

/-- ★ **The exact count partition**: `leafSectorCount = span + sub` at every level. -/
theorem leafSectorCount_eq_span_add_sub (π : O) (m : ℕ) (σ : FactorizationType)
    (M : ℕ) :
    leafSectorCount O π m σ M
      = leafSpanCount O π m σ M + leafSubCount O π m σ M := by
  classical
  haveI : Fintype (Coeff O m (M + m)) := Fintype.ofFinite _
  have h0 : leafSectorCount O π m σ M = Nat.card (leafSector O π m σ M) := rfl
  rw [h0, leafSector_eq_span_union_sub π m σ M]
  unfold leafSpanCount leafSubCount
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_union_eq (leafSpan_disjoint_sub π m σ M) (Set.toFinite _)
      (Set.toFinite _)]

end Partition

section PartitionShape

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★★ **THE SHAPE OF A SPANNING LEAF CELL** (the workhorse): a spanning leaf cell
forces `σ = ⟨{(e', d)}⟩` with `e'·d = m` and `d ≥ 2`, and the cell lies in the
`(h, e', d)` leaf box.  (`d = 1` would place the cell in CN4's pure-face box,
excluded from the carrier; the type pin is RIS's spanning decision +
`decidedAt_unique`.) -/
theorem leafSpan_shape {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ leafSpanSector O π m σ M) :
    ∃ h e' d : ℕ, σ = ⟨{(e', d)}⟩ ∧ m = e' * d ∧ 2 ≤ d ∧ 1 ≤ h ∧ h < e'
      ∧ Nat.Coprime h e' ∧ c ∈ leafIrrBox π m (M + m) h e' d := by
  obtain ⟨hcar, h, e', hF, hirr, hA0⟩ := hc
  have hsup := minFaceAt_support hF
  have hh1 : 1 ≤ h := hF.1
  have hhe : h < e' := hF.2.1
  have hcop : Nat.Coprime h e' := hF.2.2.1
  have hAm : NPAttains c h e' m := hF.2.2.2.2.1
  have hvis : NPVisibleAt c h e' := hF.2.2.2.2.2
  have he'0 : 0 < e' := by omega
  have hmK : m ≤ M + m := by omega
  -- the corner equation `e'·v₀ = h·m`
  have hnp0 : npHeight c 0 = resOrd (c ⟨0, hm0⟩) := by
    have h5 := npHeight_coe c ⟨0, hm0⟩
    simpa using h5
  have hv0eq : e' * resOrd (c ⟨0, hm0⟩) = h * m := by
    have h1 := hA0.2
    rw [hnp0, hsup] at h1
    omega
  -- coprimality forces `e' ∣ m`
  obtain ⟨d, hd⟩ : e' ∣ m :=
    hcop.symm.dvd_of_dvd_mul_left ⟨resOrd (c ⟨0, hm0⟩), hv0eq.symm⟩
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h1
    · rw [Nat.mul_zero] at hd
      omega
    · exact h1
  have hv0 : resOrd (c ⟨0, hm0⟩) = h * d := by
    have h1 : e' * resOrd (c ⟨0, hm0⟩) = e' * (h * d) := by
      rw [hv0eq, hd]
      ring
    exact Nat.eq_of_mul_eq_mul_left he'0 h1
  -- the cone membership and the digit-genre transport
  have hbox : ∀ i : Fin m, h * (m - (i : ℕ)) ≤ e' * resOrd (c i) := fun i =>
    minFaceAt_min hF i
  have hirrLeaf : Irreducible (leafResPoly π h e' d c) :=
    (irreducible_classResidualPoly_iff hπ (by omega) hhe hd0 hd hm0 hmK hbox hv0).mp
      hirr
  -- `d ≥ 2`: else the cell is a pure-face box member, outside the carrier
  have hd2 : 2 ≤ d := by
    by_contra hd1
    have hd1' : d = 1 := by omega
    have hde : m = e' := by rw [hd, hd1', Nat.mul_one]
    refine hcar.2 ⟨h, ?_, ?_⟩
    · -- `h ∈ faceH m`
      have hcopm : Nat.Coprime h m := by
        rw [hde]
        exact hcop
      have hmem : h ∈ Finset.filter (fun x => 1 ≤ x ∧ Nat.Coprime x m)
          (Finset.range m) :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hh1, hcopm⟩
      exact hmem
    · -- `c ∈ faceBox O m (M + m) h`
      refine ⟨?_, ?_⟩
      · rw [hnp0, hv0, hd1', Nat.mul_one]
      · intro i
        have h1 : h * (m - (i : ℕ)) ≤ e' * resOrd (c i) := hbox i
        rw [← hde] at h1
        have hnp : npHeight c (i : ℕ) = resOrd (c i) := by
          have h5 := npHeight_coe c i
          simpa using h5
        rw [hnp]
        exact h1
  -- the spanning decision pins the type
  have hstr : c ∈ levelZeroStratum O m (M + m) (X ^ m) := hcar.1.1.2
  have hdec := decidedAt_of_spanning_irr hd0 hπ hm0 (by omega : 0 < h) he'0 hcop hd
    hstr hA0 hAm hvis hirr
  have hdecσ : DecidedAt O m σ (M + m) c := hcar.1.1.1
  have hσ : σ = ⟨{(e', d)}⟩ := decidedAt_unique hdecσ hdec
  exact ⟨h, e', d, hσ, hd, hd2, hh1, hhe, hcop, hbox, hirrLeaf⟩

/-- `faceH` membership, unfolded (the filter idiom). -/
private theorem mem_faceH_iff {e' h : ℕ} :
    h ∈ faceH e' ↔ (h < e' ∧ 1 ≤ h ∧ Nat.Coprime h e') := by
  classical
  constructor
  · intro hmem
    have hmem' : h ∈ Finset.filter (fun h => 1 ≤ h ∧ Nat.Coprime h e')
        (Finset.range e') := hmem
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hmem'
    exact ⟨Finset.mem_range.mp h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have hmem' : h ∈ Finset.filter (fun h => 1 ≤ h ∧ Nat.Coprime h e')
        (Finset.range e') :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2, h3⟩
    exact hmem'

/-- ★★ **The spanning half IS the box bank** at the matching singleton type. -/
theorem leafSpanSector_eq_biUnion {π : O} (hπ : Irreducible π) {e' d : ℕ}
    (he'0 : 0 < e') (hd2 : 2 ≤ d) {σ : FactorizationType} (hσ : σ = ⟨{(e', d)}⟩)
    {m : ℕ} (hm : m = e' * d) (M : ℕ) :
    leafSpanSector O π m σ M = ⋃ h ∈ faceH e', leafIrrBox π m (M + m) h e' d := by
  have hd0 : 0 < d := by omega
  have hm0 : 0 < m := by
    rw [hm]
    exact Nat.mul_pos he'0 hd0
  have hmK : m ≤ M + m := by omega
  ext c
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro hc
    obtain ⟨h₂, e₂, d₂, hσ₂, hm₂, hd₂, hh₂, hhe₂, hcop₂, hbox₂⟩ :=
      leafSpan_shape hπ hm0 hc
    rw [hσ] at hσ₂
    have hdata : ({(e', d)} : Multiset (ℕ × ℕ)) = {(e₂, d₂)} :=
      congrArg FactorizationType.data hσ₂
    have hpair : (e', d) = (e₂, d₂) := Multiset.singleton_inj.mp hdata
    have he'eq : e₂ = e' := (congrArg Prod.fst hpair).symm
    have hdeq : d₂ = d := (congrArg Prod.snd hpair).symm
    subst he'eq
    subst hdeq
    exact ⟨h₂, mem_faceH_iff.mpr ⟨hhe₂, hh₂, hcop₂⟩, hbox₂⟩
  · rintro ⟨h, hhmem, hbox⟩
    obtain ⟨hhe, hh1, hcop⟩ := mem_faceH_iff.mp hhmem
    have hh0 : 0 < h := hh1
    have hhd : h * d < m := by
      rw [hm]
      have h1 : h + 1 ≤ e' := hhe
      have h2 := Nat.mul_le_mul h1 (le_refl d)
      have h3 : h * d + d = (h + 1) * d := by ring
      omega
    -- the exact corner and the face data
    have hv0 := leafIrrBox_corner hπ hh0 hhe hd2 hm hm0 hmK hbox
    obtain ⟨hsup, hA0, hAm, hvis⟩ :=
      leafCone_face_data hh0 hhe hd0 hm hm0 hmK hbox.1 hv0
    -- the minimal face
    have hF : MinFaceAt c h e' :=
      ⟨hh1, hhe, hcop, ⟨0, m, hm0, hA0, hAm⟩, hAm, hvis⟩
    -- the class residual is irreducible (the bridge, backwards)
    have hirrC : Irreducible (classResidualPoly π c h e') :=
      (irreducible_classResidualPoly_iff hπ hh0 hhe hd0 hm hm0 hmK hbox.1 hv0).mpr
        hbox.2
    -- stratum membership
    have hstr : c ∈ levelZeroStratum O m (M + m) (X ^ m) := by
      refine (mem_stratum_X_pow_iff (by omega : 1 ≤ M + m) c).2 fun i => ?_
      have h1 : h * (m - (i : ℕ)) ≤ e' * resOrd (c i) := hbox.1 i
      have h2 : 0 < h * (m - (i : ℕ)) :=
        Nat.mul_pos hh0 (by have := i.isLt; omega)
      rcases Nat.eq_zero_or_pos (resOrd (c i)) with h3 | h3
      · rw [h3, Nat.mul_zero] at h1
        omega
      · exact h3
    -- the decision
    have hdec := decidedAt_of_spanning_irr hd0 hπ hm0 hh0 he'0 hcop hm hstr hA0
      hAm hvis hirrC
    have hdecσ : c ∈ decidedSet O m σ (M + m) := by
      show DecidedAt O m σ (M + m) c
      rw [hσ]
      exact hdec
    -- shallow
    have hsh : c ∈ shallowSet O m (M + m) := by
      refine ⟨⟨0, hm0⟩, ?_⟩
      have h1 : ((⟨0, hm0⟩ : Fin m) : ℕ) = 0 := rfl
      rw [h1, hv0, Nat.sub_zero]
      exact hhd
    -- not a pure-face box member
    have hnp : c ∉ pureFaceSet O m (M + m) := by
      rintro ⟨h'', hmem'', hbox''⟩
      have hnp0 : npHeight c 0 = resOrd (c ⟨0, hm0⟩) := by
        have h5 := npHeight_coe c ⟨0, hm0⟩
        simpa using h5
      have hv0'' : h'' = h * d := by
        have h1 := hbox''.1
        rw [hnp0, hv0] at h1
        omega
      have hmem2 : h'' ∈ Finset.filter (fun x => 1 ≤ x ∧ Nat.Coprime x m)
          (Finset.range m) := hmem''
      obtain ⟨-, -, hcop''⟩ := Finset.mem_filter.mp hmem2
      have hdd : d ∣ Nat.gcd h'' m := by
        refine Nat.dvd_gcd ⟨h, by rw [hv0'', Nat.mul_comm]⟩ ⟨e', by rw [hm, Nat.mul_comm]⟩
      rw [Nat.Coprime] at hcop''
      rw [hcop''] at hdd
      have := Nat.le_of_dvd (by omega) hdd
      omega
    exact ⟨⟨⟨⟨hdecσ, hstr⟩, hsh⟩, hnp⟩, h, e', hF, hirrC, hA0⟩

/-- ★ **The spanning half is EMPTY off the matching singleton types.** -/
theorem leafSpanSector_eq_empty {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    {σ : FactorizationType} {M : ℕ}
    (hσ : ∀ e' d : ℕ, σ = ⟨{(e', d)}⟩ → m = e' * d → 2 ≤ d → False) :
    leafSpanSector O π m σ M = (∅ : Set (Coeff O m (M + m))) := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hc
  obtain ⟨h₂, e₂, d₂, hσ₂, hm₂, hd₂, -, -, -, -⟩ := leafSpan_shape hπ hm0 hc
  exact hσ e₂ d₂ hσ₂ hm₂ hd₂

/-- The biUnion count helper (IFCG53's private replay). -/
private theorem ncard_biUnion_eq {α ι : Type*} [Finite α] (s : Finset ι)
    (f : ι → Set α)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    (⋃ i ∈ s, f i).ncard = ∑ i ∈ s, (f i).ncard := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have hcons : (⋃ i ∈ Finset.cons a s ha, f i) = f a ∪ ⋃ i ∈ s, f i := by
        ext x
        simp [Set.mem_iUnion]
      have hd : Disjoint (f a) (⋃ i ∈ s, f i) := by
        rw [Set.disjoint_right]
        intro x hx hxa
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
        exact (Set.disjoint_left.1 (hdisj a (Finset.mem_cons_self a s) i
          (Finset.mem_cons_of_mem hi) (by rintro rfl; exact ha hi))) hxa hxi
      rw [hcons, Set.ncard_union_eq hd, Finset.sum_cons,
        ih (fun i hi j hj hij => hdisj i (Finset.mem_cons_of_mem hi) j
          (Finset.mem_cons_of_mem hj) hij)]

/-- The boxes at distinct admissible slopes are disjoint (the exact corner pins
`v₀ = h·d`). -/
theorem leafIrrBox_disjoint {π : O} (hπ : Irreducible π) {e' d : ℕ}
    (hd2 : 2 ≤ d) {m K : ℕ} (hm : m = e' * d) (hm0 : 0 < m) (hmK : m ≤ K)
    {h₁ h₂ : ℕ} (h₁mem : h₁ ∈ faceH e') (h₂mem : h₂ ∈ faceH e') (hne : h₁ ≠ h₂) :
    Disjoint (leafIrrBox π m K h₁ e' d) (leafIrrBox π m K h₂ e' d) := by
  obtain ⟨hhe₁, hh₁, -⟩ := mem_faceH_iff.mp h₁mem
  obtain ⟨hhe₂, hh₂, -⟩ := mem_faceH_iff.mp h₂mem
  rw [Set.disjoint_left]
  intro c hc₁ hc₂
  have hv₁ := leafIrrBox_corner hπ hh₁ hhe₁ hd2 hm hm0 hmK hc₁
  have hv₂ := leafIrrBox_corner hπ hh₂ hhe₂ hd2 hm hm0 hmK hc₂
  rw [hv₁] at hv₂
  have : h₁ = h₂ := Nat.eq_of_mul_eq_mul_right (by omega) hv₂
  exact hne this

/-- ★★ **THE SPANNING COUNT** (case A): the exact necklace-monomial bank. -/
theorem card_leafSpanSector {π : O} (hπ : Irreducible π) {e' d : ℕ}
    (he'0 : 0 < e') (hd2 : 2 ≤ d) {σ : FactorizationType} (hσ : σ = ⟨{(e', d)}⟩)
    {m : ℕ} (hm : m = e' * d) (M : ℕ) :
    leafSpanCount O π m σ M
      = ∑ h ∈ faceH e',
          Nat.card (Uniformity.Density.IFCG4.IrredOfDeg (IsLocalRing.ResidueField O) d)
            * residueCard O ^ (m * (M + m) - wLeaf h e' d) := by
  have hd0 : 0 < d := by omega
  have hm0 : 0 < m := by
    rw [hm]
    exact Nat.mul_pos he'0 hd0
  have hmK : m ≤ M + m := by omega
  unfold leafSpanCount
  rw [leafSpanSector_eq_biUnion hπ he'0 hd2 hσ hm M, Nat.card_coe_set_eq,
    ncard_biUnion_eq (faceH e') _
      (fun i hi j hj hij => leafIrrBox_disjoint hπ hd2 hm hm0 hmK hi hj hij)]
  refine Finset.sum_congr rfl fun h hmem => ?_
  obtain ⟨hhe, hh1, -⟩ := mem_faceH_iff.mp hmem
  rw [← Nat.card_coe_set_eq, card_leafIrrBox hπ hh1 hhe hd0 hm hmK]

end PartitionShape

/-! ## §5 — ★★★ the spanning law fires; the sub-face remainder is named -/

section Laws

/-- The leaf weight is bounded by `m²` (`m = e'·d`) — the box exponents stay
admissible at every level `K ≥ m`. -/
theorem wLeaf_le_sq {h e' d : ℕ} (hh : 0 < h) (hhe : h < e') (hd0 : 0 < d) :
    wLeaf h e' d ≤ (e' * d) * (e' * d) := by
  have he'0 : 0 < e' := by omega
  have hhd : h * d + 1 ≤ e' * d := by
    have h1 : h + 1 ≤ e' := hhe
    have h2 := Nat.mul_le_mul h1 (le_refl d)
    have h3 : h * d + d = (h + 1) * d := by ring
    omega
  unfold wLeaf
  calc ∑ i ∈ Finset.range (e' * d),
        (tLeaf h e' (e' * d) i + if e' ∣ i then 1 else 0)
      ≤ ∑ _i ∈ Finset.range (e' * d), (h * d + 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := tLeaf_le_corner he'0 h d i
        by_cases hdvd : e' ∣ i
        · rw [if_pos hdvd]
          omega
        · rw [if_neg hdvd]
          omega
    _ = (e' * d) * (h * d + 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ (e' * d) * (e' * d) := Nat.mul_le_mul (le_refl (e' * d)) hhd

/-- ★ **The necklace monomial is a `ZcURLim` family**: the constant
`N_d(q)/q^w`, with the pair `(necklacePoly d, X^w)` (IFCG19's census evaluated). -/
theorem zcURLim_necklace_monomial (d w : ℕ) (hd : 1 ≤ d) :
    ZcURLim (fun O _ _ _ _ _ _ _ =>
      (Nat.card (Uniformity.Density.IFCG4.IrredOfDeg (IsLocalRing.ResidueField O) d) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ w) := by
  refine ⟨necklacePoly d, Polynomial.X ^ w, pow_ne_zero _ Polynomial.X_ne_zero, ?_⟩
  intro O _ _ _ _ _
  letI : Fintype (IsLocalRing.ResidueField O) := Fintype.ofFinite _
  have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
  have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hden : (Polynomial.X ^ w : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) ≠ 0 := by
    rw [Polynomial.eval_pow, Polynomial.eval_X]
    exact pow_ne_zero _ hqQ
  refine ⟨hden, ?_⟩
  intro π hπ
  have hqcard : residueCard O = Fintype.card (IsLocalRing.ResidueField O) :=
    Nat.card_eq_fintype_card
  have hnum : (necklacePoly d).eval ((residueCard O : ℕ) : ℚ)
      = (Nat.card (Uniformity.Density.IFCG4.IrredOfDeg (IsLocalRing.ResidueField O) d) : ℚ) := by
    rw [hqcard, necklacePoly_eval_card (IsLocalRing.ResidueField O) d hd]
  have hval : (((necklacePoly d).eval ((residueCard O : ℕ) : ℚ)
        / (Polynomial.X ^ w : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
      = (Nat.card (Uniformity.Density.IFCG4.IrredOfDeg (IsLocalRing.ResidueField O) d) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ w := by
    rw [hnum, Polynomial.eval_pow, Polynomial.eval_X]
    push_cast
    ring
  rw [hval]
  exact tendsto_const_nhds

/-- ★★★ **THE SPANNING LAW, UNCONDITIONAL**: the normalized spanning-leaf count is
a `ZcURLim` family at EVERY `(m, σ)` — value `Σ_{h ∈ faceH e'} N_d(q)/q^(wLeaf h e' d)`
at the matching singleton type `σ = ⟨{(e', d)}⟩` (`e'·d = m`, `d ≥ 2`), and `0`
elsewhere.  No premises: the count is EXACT at every finite level. -/
theorem zcURLim_leafSpanFam (m : ℕ) (hm0 : 0 < m) (σ : FactorizationType) :
    ZcURLim (fun O _ _ _ _ _ π M =>
      (leafSpanCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) := by
  by_cases hex : ∃ e' d : ℕ, σ = ⟨{(e', d)}⟩ ∧ m = e' * d ∧ 2 ≤ d
  · obtain ⟨e', d, hσ, hm, hd2⟩ := hex
    have hd0 : 0 < d := by omega
    have he'0 : 0 < e' := by
      rcases Nat.eq_zero_or_pos e' with rfl | h1
      · rw [Nat.zero_mul] at hm
        omega
      · exact h1
    refine (ZcURLim_sum (faceH e')
        (fun h => fun O _ _ _ _ _ _ _ =>
          (Nat.card (Uniformity.Density.IFCG4.IrredOfDeg (IsLocalRing.ResidueField O) d) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d))
        (fun h _ => zcURLim_necklace_monomial d _ (by omega))).congr ?_
    intro O _ _ _ _ _ π hπ M
    have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
    have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [card_leafSpanSector hπ he'0 hd2 hσ hm M]
    have key : ∀ h ∈ faceH e',
        ((Nat.card (Uniformity.Density.IFCG4.IrredOfDeg (IsLocalRing.ResidueField O) d)
            * residueCard O ^ (m * (M + m) - wLeaf h e' d) : ℕ) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
        = (Nat.card (Uniformity.Density.IFCG4.IrredOfDeg (IsLocalRing.ResidueField O) d) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d) := by
      intro h hmem
      obtain ⟨hhe, hh1, -⟩ := mem_faceH_iff.mp hmem
      have hwle : wLeaf h e' d ≤ m * (M + m) := by
        have h1 := wLeaf_le_sq (h := h) (e' := e') (d := d) hh1 hhe hd0
        rw [← hm] at h1
        have h2 : m * m ≤ m * (M + m) := Nat.mul_le_mul (le_refl m) (by omega)
        omega
      have hpow : ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
          = ((residueCard O : ℕ) : ℝ) ^ (m * (M + m) - wLeaf h e' d)
            * ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d) := by
        rw [← pow_add]
        congr 1
        omega
      have h1 : ((residueCard O : ℕ) : ℝ) ^ (m * (M + m) - wLeaf h e' d) ≠ 0 :=
        pow_ne_zero _ hqR
      have h2 : ((residueCard O : ℕ) : ℝ) ^ (wLeaf h e' d) ≠ 0 := pow_ne_zero _ hqR
      push_cast
      rw [hpow]
      field_simp
    rw [Nat.cast_sum, Finset.sum_div]
    exact (Finset.sum_congr rfl key).symm
  · refine ZcURLim_zero.congr ?_
    intro O _ _ _ _ _ π hπ M
    have h1 : leafSpanSector O π m σ M = (∅ : Set (Coeff O m (M + m))) :=
      leafSpanSector_eq_empty hπ hm0
        (fun e' d hσ hm hd2 => hex ⟨e', d, hσ, hm, hd2⟩)
    have h2 : leafSpanCount O π m σ M = 0 := by
      unfold leafSpanCount
      rw [h1]
      simp
    rw [h2]
    simp

/-- ★★★ **THE NAMED REMAINDER — the sub-face leaf law at `(m, σ)`**: a uniform
rational limit for the normalized count of the NON-spanning leaf cells (minimal
face not attained at `0`).  This is the exact open content of master row 5 after
this file: the face digit box at `(h, e', d)`, `e'·d < m`, convolved with the
sub-face rest (the mass-`(m − e'·d)` classes above the face line at the
complementary type) — the class-level two-block correspondence territory. -/
def LeafSubfaceLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (leafSubCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- ★★★ **THE RE-BASE**: the sub-face law fires the FULL leaf sector law — the
spanning (necklace) half is closed unconditionally, so `LeafSectorLaw`'s open
content is EXACTLY `LeafSubfaceLaw`. -/
theorem leafSectorLaw_of_subface {m : ℕ} (hm0 : 0 < m) (σ : FactorizationType)
    (hsub : LeafSubfaceLaw m σ) : LeafSectorLaw m σ := by
  refine ((zcURLim_leafSpanFam m hm0 σ).add hsub).congr ?_
  intro O _ _ _ _ _ π hπ M
  rw [leafSectorCount_eq_span_add_sub π m σ M]
  push_cast
  rw [add_div]

end Laws

/-! ## §6 — ★★★ THE MASTER RECOMPUTED: row 5 shrinks to the sub-face law

IFCG55's `decidedSliceAt_all_of_MASTER` consumed `hLeaf : … → LeafSectorLaw e σ`.
The spanning (necklace) half of that row is now MACHINE-CHECKED
(`zcURLim_leafSpanFam`, no premises), so the master premise WEAKENS to
`LeafSubfaceLaw e σ` under the same guards.  The surviving premise surface of the
census (and, through ID12, of the whole proof):

| # | master premise | status |
|---|---|---|
| 1 | `FactorCorrespondenceAt D`, every `D ≥ 2` | THE STAGED CITE (owner gate; CTS) |
| 2 | `EisFullSpanRemainderLaw m σ`, composite `m ≥ 6`, guarded | open (ASM) |
| 3 | `SplitConvolutionDefectLaw e σ`, `e ≥ 5`, guarded | open (IFCG38) |
| 4 | `PowerConvolutionDefectLaw e σ`, `e ≥ 5`, guarded | open (IFCG44) |
| 5 | `LeafSubfaceLaw e σ`, `e ≥ 5`, guarded | open — STRICTLY SMALLER than IFCG55's row 5: only the NON-spanning leaf cells (the sub-face convolution) remain; the spanning necklace census is closed (this file) |
-/

section Master

/-- ★★★ **THE CENSUS MASTER, ROW 5 RECOMPUTED**: the all-degree decided slice from
the four unchanged master premises + the strictly smaller `LeafSubfaceLaw`
(the spanning necklace half of IFCG55's `hLeaf` is discharged by
`zcURLim_leafSpanFam`). -/
theorem decidedSliceAt_all_of_MASTER'
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
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → LeafSubfaceLaw e σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG55.decidedSliceAt_all_of_MASTER hFC hEis hSD hPD
    (fun e he hsm σ hσ hwit hram =>
      leafSectorLaw_of_subface (by omega : 0 < e) σ
        (hLeafSub e he hsm σ hσ hwit hram))

universe uW uG uKt uL

/-- ★★★ **THE CAPSTONE MASTER, ROW 5 RECOMPUTED**: `CapstoneHypotheses n` from
{ladder, deepTwist} + the four unchanged census premises + `LeafSubfaceLaw`.
(IFCG55's `capstoneHypotheses_of_MASTER` with the leaf row re-based; ID12's honesty
frame applies verbatim.) -/
theorem capstoneHypotheses_of_MASTER' (n : ℕ)
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
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → LeafSubfaceLaw e σ) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  Uniformity.Density.IFCG55.capstoneHypotheses_of_MASTER n hladder hdeepTwist hFC
    hEis hSD hPD
    (fun e he hsm σ hσ hwit hram =>
      leafSectorLaw_of_subface (by omega : 0 < e) σ
        (hLeafSub e he hsm σ hσ hwit hram))

end Master

end Uniformity.Density.IFCG57

end

/-! ## AXCHECK FOOTER — expected: §§0–3 (the kit, the digit polynomial, THE BRIDGE,
the necklace count) and the §4 partition arithmetic are pure Lean core
`{propext, Classical.choice, Quot.sound}`; the §4 shape/identity theorems, the §5
laws, and the §6 census master expect Lean core PLUS exactly the owner-signed
gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42, inherited
through the landed IFCG26/28/37 transports — never re-consumed); the §6 capstone
master additionally inherits exactly `agnprw_termination` (ID12, previously
declared).  The C.33 cites must NOT occur. -/

#print axioms Uniformity.Density.IFCG57.tLeaf_mul
#print axioms Uniformity.Density.IFCG57.leafResPoly_eq_iff
#print axioms Uniformity.Density.IFCG57.coeff_zero_ne_zero_of_irreducible
#print axioms Uniformity.Density.IFCG57.leafCone_face_data
#print axioms Uniformity.Density.IFCG57.classResidualPoly_eq_leafResPoly
#print axioms Uniformity.Density.IFCG57.irreducible_classResidualPoly_iff
#print axioms Uniformity.Density.IFCG57.mem_leafFiber_iff
#print axioms Uniformity.Density.IFCG57.card_leafFiber
#print axioms Uniformity.Density.IFCG57.card_leafIrrBox
#print axioms Uniformity.Density.IFCG57.leafIrrBox_corner
#print axioms Uniformity.Density.IFCG57.leafSector_eq_span_union_sub
#print axioms Uniformity.Density.IFCG57.leafSectorCount_eq_span_add_sub
#print axioms Uniformity.Density.IFCG57.leafSpan_shape
#print axioms Uniformity.Density.IFCG57.leafSpanSector_eq_biUnion
#print axioms Uniformity.Density.IFCG57.leafSpanSector_eq_empty
#print axioms Uniformity.Density.IFCG57.leafIrrBox_disjoint
#print axioms Uniformity.Density.IFCG57.card_leafSpanSector
#print axioms Uniformity.Density.IFCG57.wLeaf_le_sq
#print axioms Uniformity.Density.IFCG57.zcURLim_necklace_monomial
#print axioms Uniformity.Density.IFCG57.zcURLim_leafSpanFam
#print axioms Uniformity.Density.IFCG57.leafSectorLaw_of_subface
#print axioms Uniformity.Density.IFCG57.decidedSliceAt_all_of_MASTER'
#print axioms Uniformity.Density.IFCG57.capstoneHypotheses_of_MASTER'
