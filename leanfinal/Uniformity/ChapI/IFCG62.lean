/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapI.IFCG60

/-!
# Uniformity.ChapI.IFCG62 — UNIT EFR: the mixed-lattice instruments for the
Eisenstein full-span remainder — the per-frame partition, the reduction of
`EisFullSpanRemainderLaw` to named `(h, e', d)`-frame laws, the compositum
coordinate lattice, and the composed `(1, d)` criterion

**UNIT EFR** (wave C, 2026-08-31; design record `runs/wave-c/verdict_EFR.md`).
ASM (`IFCG51`) named `EisFullSpanRemainderLaw m σ` — the `ZcURLim` of the
non-Eisenstein-frame part of the full-span power sector (the `h ≥ 2` slopes and the
`deg ψ ≥ 2` residual root fields) — as the census master's row 2 at composite
`m ≥ 6`.  PSL4 §5 recorded this territory's exact open instruments: the `(h, 1)`
digit criterion (landed, ring-free), the `(1, d)` compositum value transport
(landed), and the coordinate lattices over the compositum (open).  This file lands:

* **§1–§3 THE PER-FRAME REDUCTION**: every remainder class carries canonical frame
  data `(h, e', d)` (slope numerator, denominator, residual root-field degree) with
  `e'·d ∣ m`, `k := m/(e'·d) ≥ 2` and `(h, d) ≠ (1, 1)`; the carriers `mixedFace`
  partition the remainder EXACTLY (`remainder_eq_biUnion`, `card_remainder_partition`),
  and the named per-frame laws `MixedFaceLaw m h e' d σ` fire the row-2 law
  (★★★ `eisFullSpanRemainderLaw_of_mixedFaceLaws`).  The frame index is the
  machine-checked Finset `mixedFrames m` (`= ∅` at `m = 4`, `= {(2,3,1)}` at `m = 6`,
  `= {(1,2,2), (3,4,1)}` at `m = 8` — kernel-decided anchors).  Off the degree
  (`σ.degree ≠ m`) both the frame laws and the row-2 law are UNCONDITIONAL.
* **§4 THE MIXED LATTICE** (charge item 1): the coordinate lattice over the
  compositum `O₂ = AdjoinRoot (eisKey (algebraMap π) c₁ e')` over `O₁ = AdjoinRoot φ`
  — ★★ `compositum_root_pow_dvd_mk_iff`: `α₂^w ∣ mk P ⟺ π^{⌈(w−i)/e'⌉} ∣ (Bᵢ)ⱼ`,
  THE COMPOSED DIVISIBILITY CEILINGS (the Eisenstein-stage ceiling of
  `eis_root_pow_dvd_mk_iff` composed with the unramified-stage coefficient read
  `unram_pow_dvd_mk_iff`).  This is exactly PSL3's recorded missing instrument
  ("the RINGS are landed, their coordinate lattices are not").
* **§5 THE GENERAL-TARGET DIGIT READING** (charge item 2, the box reading): at any
  slope `h/e'` under the side pins, `xres = R` for ANY monic degree-`D` target `R`
  ⟺ the `D` lattice digits at heights `h·(D−t)` read `R`'s coefficients
  (★★ `xres_eq_iff_digits_target`); instantiated at `R = ψ^k` this is the mixed
  faces' box reading (★ `xres_eq_psi_pow_iff_digits`), recovering the landed
  `(h, 1)` and `(1, 1)` criteria.
* **§6 THE COMPOSED `(1, d)` CRITERION** (charge item 2, the tower composition):
  ★★ `compositum_transfer_digits_base` — the deep recentred box over the COMPOSITUM,
  read through the mixed lattice into base-ring composed ceilings, is equivalent to
  the digit equations over `O₁` — `eis_transfer_digits_iff` instantiated at the
  unramified stage (the h = 1, d ≥ 2 tower route around the single-ring obstruction).
* **§7 THE CENSUS WIRE**: ★★★ `decidedSliceAt_all_of_MASTER_MIXED` — IFCG60's
  master with row 2 re-based onto the per-frame `MixedFaceLaw` premises.

## Honesty fence

`EisFullSpanRemainderLaw m σ` at composite `m ≥ 6`, `σ.degree = m` did NOT fire
unconditionally: the reduction re-bases row 2 onto the per-frame laws
`MixedFaceLaw m h e' d σ` at `(h, e', d) ∈ mixedFrames m`, and the instruments for
their discharge are landed here (§4–§6), but the per-frame count/decision transports
(the analogues of `cellTransport`/`transport_decidedAt_iff` at `h ≥ 2` and over the
compositum) remain the named open set.  Nothing was weakened: the row-2 Prop is
consumed byte-identically, and the reduction is an exact partition identity.

## Axiom fence

Everything composes landed Lean-core material; expected footprint: pure Lean core
`{propext, Classical.choice, Quot.sound}` on every §1–§6 declaration.  §7's master
wire inherits IFCG60's footprint (Lean core + the owner-signed B.42 cite, inherited,
never re-consumed).  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG62

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport classNPSupport_le)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_sum shallowSet
  mem_stratum_X_pow_iff pureFaceSet ConeRemainderLaw npHeight_coe)
open Uniformity.Density.IFCG27 (adjoinRoot_isDVR adjoinRoot_maximalIdeal_eq
  adjoinRoot_isAdicComplete adjoinRoot_finite_residueField residueCard_adjoinRoot)
open Uniformity.Density.IFCG29 (irreducible_algebraMap_adjoinRoot)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_support minFaceAt_min
  minFaceAt_unique classResidualPoly classResidualPoly_eq
  classResidualPoly_natDegree_pos powerSector remainderCarrier)
open Uniformity.Density.IFCG37 (xres)
open Uniformity.Density.IFCG38 (classResidualPoly_monic SplitConvolutionDefectLaw)
open Uniformity.Density.IFCG39 (powerSector_data powerSector_mass_drop
  eisKey eisKey_monic eisKey_natDegree eis_root_pow_dvd_mk_iff)
open Uniformity.Density.IFCG43 (eis_transfer_digits_iff)
open Uniformity.Density.IFCG44 (fullSpan_corner minFaceAt_of_lattice
  powerSectorFull PowerFullSpanLaw PowerConvolutionDefectLaw)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG51 (eisFace EisFullSpanRemainderLaw)
open Uniformity.Density.IFCG57 (LeafSubfaceLaw)

/-! ## §0 — kit (private replicas of the established supply) -/

section Kit

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

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- A proper power of a positive-degree monic is never irreducible (the general-`d`
replay of IFCG51's linear-power exclusion). -/
private theorem not_irreducible_monic_pow
    {ψ : Polynomial (resField (X : Polynomial O))}
    (hd : 1 ≤ ψ.natDegree) {k : ℕ} (hk : 2 ≤ k) :
    ¬ Irreducible (ψ ^ k) := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  intro hirr
  have hsplit : ψ ^ k = ψ * ψ ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rcases hirr.isUnit_or_isUnit hsplit with hu | hu
  · have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_pow] at hdeg
    have h1 : 1 * 1 ≤ (k - 1) * ψ.natDegree :=
      Nat.mul_le_mul (by omega) hd
    omega

/-- Prime-power rigidity over the residual field: equal proper powers of monic
irreducibles have EQUAL bases (UFD: the base divides the other power, primes are
associated, monicity upgrades to equality). -/
private theorem monic_irreducible_pow_eq
    {ψ ψ' : Polynomial (resField (X : Polynomial O))}
    (hψm : ψ.Monic) (hψ : Irreducible ψ) (hψ'm : ψ'.Monic) (hψ' : Irreducible ψ')
    {k k' : ℕ} (hk : 1 ≤ k) (heq : ψ ^ k = ψ' ^ k') : ψ = ψ' := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hdvd : ψ ∣ ψ' ^ k' := by
    rw [← heq]
    exact dvd_pow_self ψ (by omega)
  have hψp : Prime ψ := hψ.prime
  have hdvd' : ψ ∣ ψ' := hψp.dvd_of_dvd_pow hdvd
  exact Polynomial.eq_of_monic_of_associated hψm hψ'm
    (hψ.associated_of_dvd hψ' hdvd')

end Kit

/-! ## §1 — the mixed-face carriers, the per-frame laws, and the frame index -/

section Carrier

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The σ-decided mixed-face carrier** at frame `(h, e', d)`: minimal face `(h, e')`,
canonical residual an EXACT `m/(e'·d)`-th power of a monic irreducible of degree `d`
with nonzero constant term, decided at `σ`.  At `(h, d) = (1, 1)` this is IFCG51's
`eisFace`; the frames with `(h, d) ≠ (1, 1)` tile the non-Eisenstein remainder. -/
def mixedFace (π : O) (m h e' d N : ℕ) (σ : FactorizationType) :
    Set (Coeff O m N) :=
  {c | MinFaceAt c h e'
    ∧ (∃ ψ : Polynomial (resField (X : Polynomial O)),
        ψ.Monic ∧ Irreducible ψ ∧ ψ.natDegree = d ∧ ψ.coeff 0 ≠ 0
          ∧ classResidualPoly π c h e' = ψ ^ (m / (e' * d)))
    ∧ DecidedAt O m σ N c}

end Carrier

/-- ★ **THE PER-FRAME LAW — `MixedFaceLaw m h e' d σ`**: the uniform rational limit
of the normalized frame-carrier count.  The frames in `mixedFrames m` are row 2's
exact per-axis content: `(h ≥ 2, d = 1)` the fractional-slope faces, `(1, d ≥ 2)`
the residual root-field faces (the compositum territory), `(h ≥ 2, d ≥ 2)` the
mixed faces. -/
def MixedFaceLaw (m h e' d : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (Nat.card (mixedFace π m h e' d (M + m) σ) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- **The frame index**: all `(h, e', d)` with `1 ≤ h < e'` coprime, `1 ≤ d`,
`e'·d ∣ m`, residual multiplicity `k = m/(e'·d) ≥ 2`, EXCLUDING the Eisenstein
frame `(h, d) = (1, 1)` (IFCG51's landed territory). -/
def mixedFrames (m : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    (fun p => 1 ≤ p.1 ∧ p.1 < p.2.1 ∧ Nat.gcd p.1 p.2.1 = 1 ∧ 1 ≤ p.2.2
      ∧ (p.2.1 * p.2.2) ∣ m ∧ 2 ≤ m / (p.2.1 * p.2.2)
      ∧ ¬(p.1 = 1 ∧ p.2.2 = 1))

/-- Frame membership is exactly the seven arithmetic clauses (the range bounds are
implied: `2 ≤ m/(e'·d)` forces `0 < e'·d ≤ m` and `0 < m`). -/
theorem mem_mixedFrames_iff {m : ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ mixedFrames m
      ↔ 1 ≤ p.1 ∧ p.1 < p.2.1 ∧ Nat.Coprime p.1 p.2.1 ∧ 1 ≤ p.2.2
        ∧ (p.2.1 * p.2.2) ∣ m ∧ 2 ≤ m / (p.2.1 * p.2.2)
        ∧ ¬(p.1 = 1 ∧ p.2.2 = 1) := by
  unfold mixedFrames
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have hed : 0 < p.2.1 * p.2.2 := by
      rcases Nat.eq_zero_or_pos (p.2.1 * p.2.2) with h0 | h0
      · rw [h0] at h6
        simp at h6
      · exact h0
    have hedm : p.2.1 * p.2.2 ≤ m := by
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0
          rw [Nat.zero_div] at h6
          omega
        · exact h0
      exact Nat.le_of_dvd hm0 h5
    have he' : p.2.1 ≤ m := by
      calc p.2.1 = p.2.1 * 1 := (Nat.mul_one _).symm
        _ ≤ p.2.1 * p.2.2 := Nat.mul_le_mul (le_refl _) h4
        _ ≤ m := hedm
    have hd : p.2.2 ≤ m := by
      calc p.2.2 = 1 * p.2.2 := (Nat.one_mul _).symm
        _ ≤ p.2.1 * p.2.2 := Nat.mul_le_mul (by omega) (le_refl _)
        _ ≤ m := hedm
    refine ⟨?_, h1, h2, h3, h4, h5, h6, h7⟩
    rw [Finset.mem_product, Finset.mem_product]
    refine ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩

/-- **The `m = 4` frame census is EMPTY** (kernel-decided) — matching IFCG51's proved
`m = 4` emptiness of the remainder. -/
theorem mixedFrames_four : mixedFrames 4 = ∅ := by decide

/-- **The `m = 6` frame census** (kernel-decided): ONE frame, the slope-`2/3` face
`(h, e', d) = (2, 3, 1)` — ASM's recorded witness that the remainder is real. -/
theorem mixedFrames_six : mixedFrames 6 = {(2, 3, 1)} := by decide

/-- **The `m = 8` frame census** (kernel-decided): the compositum frame `(1, 2, 2)`
(residual root field `𝔽_{q²}`) and the slope-`3/4` frame `(3, 4, 1)`. -/
theorem mixedFrames_eight : mixedFrames 8 = {(1, 2, 2), (3, 4, 1)} := by decide

/-! ## §2 — the carrier sits in the full-span sector -/

section Subset

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- ★ **The mixed carrier sits in the full-span power sector** (the general-`(h, d)`
replay of IFCG51's Eisenstein-cell inclusion): a decided mixed-face member satisfies
EVERY `powerSectorFull` clause — decided, stratum, shallow, outside every pure-face
box (face uniqueness), proper-power residual, full span. -/
theorem mixedFace_subset_psf {π : O} (hπ : Irreducible π) {m h e' d : ℕ}
    (hh1 : 1 ≤ h) (hhe : h < e') (hd : 1 ≤ d) (hdvd : e' * d ∣ m)
    (hk2 : 2 ≤ m / (e' * d)) (σ : FactorizationType) (M : ℕ) :
    mixedFace π m h e' d (M + m) σ ⊆ powerSectorFull O π m σ M := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  rintro c ⟨hF, ⟨ψ, hψm, hψirr, hψdeg, hψ0, hres⟩, hdec⟩
  set k : ℕ := m / (e' * d) with hkdef
  have hmk : e' * d * k = m := Nat.mul_div_cancel' hdvd
  have hm0 : 0 < m := by
    rw [← hmk]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hmK : m ≤ M + m := by omega
  have hkd2 : 2 ≤ k * d := by
    calc 2 = 2 * 1 := by omega
      _ ≤ k * d := Nat.mul_le_mul hk2 hd
  have hem' : e' * (k * d) = m := by rw [← hmk]; ring
  -- the residual degree and the full span
  have hdegres : (classResidualPoly π c h e').natDegree = k * d := by
    rw [hres, Polynomial.natDegree_pow, hψdeg]
  have hfull : e' * (classResidualPoly π c h e').natDegree = m := by
    rw [hdegres]
    exact hem'
  -- the exact corner (for the shallow clause)
  have hcorner := fullSpan_corner hπ hF hfull hmK hm0
  rw [hdegres] at hcorner
  -- stratum
  have hstrat : c ∈ levelZeroStratum O m (M + m) (Polynomial.X ^ m) := by
    refine (mem_stratum_X_pow_iff (by omega) c).mpr fun i => ?_
    have h1 := minFaceAt_min hF i
    have h2 := i.isLt
    rcases Nat.eq_zero_or_pos (resOrd (c i)) with h0 | h3
    · exfalso
      rw [h0, Nat.mul_zero] at h1
      have h4 : 0 < h * (m - (i : ℕ)) := Nat.mul_pos (by omega) (by omega)
      omega
    · exact h3
  -- shallow
  have hsh : c ∈ shallowSet O m (M + m) := by
    refine ⟨⟨0, hm0⟩, ?_⟩
    show resOrd (c ⟨0, hm0⟩) < m - ((⟨0, hm0⟩ : Fin m) : ℕ)
    rw [hcorner]
    show h * (k * d) < m - 0
    have h1 : h * (k * d) < e' * (k * d) :=
      Nat.mul_lt_mul_of_lt_of_le hhe (le_refl (k * d)) (by omega : 0 < k * d)
    generalize hA : e' * (k * d) = A at hem' h1
    generalize hB : h * (k * d) = B at h1 ⊢
    omega
  -- outside every pure-face box
  have hpf : c ∉ pureFaceSet O m (M + m) := by
    rintro ⟨h₂, hhmem, hbox⟩
    obtain ⟨hcorner', hlat'⟩ := hbox
    have hmemfilter := hhmem
    rw [Uniformity.Density.IFCG24.faceH, Finset.mem_filter, Finset.mem_range]
      at hmemfilter
    obtain ⟨hhm, hh1', hcop'⟩ := hmemfilter
    have hlat'' : ∀ j : Fin m, h₂ * (m - (j : ℕ)) ≤ m * resOrd (c j) := by
      intro j
      have h1 := hlat' j
      rwa [npHeight_coe] at h1
    have hcorner'' : resOrd (c ⟨0, hm0⟩) = h₂ * 1 := by
      have h2 : npHeight c 0 = resOrd (c ⟨0, hm0⟩) := by
        simpa using npHeight_coe c ⟨0, hm0⟩
      rw [← h2, hcorner', Nat.mul_one]
    have hFm : MinFaceAt c h₂ m :=
      minFaceAt_of_lattice hh1' hhm hcop' (Nat.mul_one m) hmK hm0 hlat'' hcorner''
    obtain ⟨-, hem⟩ := minFaceAt_unique hF hFm
    have hDlt : e' < m := by
      have h3 : e' * 2 ≤ e' * (k * d) := Nat.mul_le_mul (le_refl e') hkd2
      generalize hA : e' * (k * d) = A at hem' h3
      omega
    omega
  -- assemble
  refine ⟨⟨⟨⟨⟨hdec, hstrat⟩, hsh⟩, hpf⟩, h, e', hF, ?_, ?_⟩, h, e', hF, hfull⟩
  · rw [hres]
    exact not_irreducible_monic_pow (by omega) hk2
  · exact ⟨ψ, k, hψirr, hk2, by rw [hres]⟩

/-- **Distinct frames are disjoint**: the minimal face pins `(h, e')` (uniqueness) and
prime-power rigidity pins `d` (equal powers of monic irreducibles share their base). -/
theorem mixedFace_disjoint {π : O} {m : ℕ} {p p' : ℕ × ℕ × ℕ}
    (hp : p ∈ mixedFrames m) (hp' : p' ∈ mixedFrames m) (hne : p ≠ p')
    (σ : FactorizationType) {N : ℕ} :
    Disjoint (mixedFace π m p.1 p.2.1 p.2.2 N σ)
      (mixedFace π m p'.1 p'.2.1 p'.2.2 N σ) := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  obtain ⟨h₁, e₁, d₁⟩ := p
  obtain ⟨h₂, e₂, d₂⟩ := p'
  rw [mem_mixedFrames_iff] at hp
  dsimp only at hp ⊢
  obtain ⟨-, -, -, -, -, hk₁, -⟩ := hp
  rw [Set.disjoint_left]
  rintro c ⟨hF, ⟨ψ, hψm, hψi, hψd, -, hres⟩, -⟩
    ⟨hF', ⟨ψ', hψm', hψi', hψd', -, hres'⟩, -⟩
  obtain ⟨hh, he⟩ := minFaceAt_unique hF hF'
  subst hh
  subst he
  have hψeq : ψ = ψ' :=
    monic_irreducible_pow_eq hψm hψi hψm' hψi' (by omega : 1 ≤ m / (e₁ * d₁))
      (hres.symm.trans hres')
  have hdd : d₁ = d₂ := by rw [← hψd, ← hψd', hψeq]
  subst hdd
  exact hne rfl

end Subset

section EisFence

-- the universe fence: IFCG51's `eisFace` quantifies `O : Type`, so its consumers
-- live here.
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]

/-- **Every frame carrier avoids every Eisenstein face**: face uniqueness forces
`h = 1`, prime-power rigidity forces the residual base linear (`d = 1`) — exactly the
excluded Eisenstein frame. -/
theorem mixedFace_disjoint_eisFace {π : O} {m : ℕ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ mixedFrames m) {e₂ D₂ : ℕ} (σ : FactorizationType) {N : ℕ} :
    Disjoint (mixedFace π m p.1 p.2.1 p.2.2 N σ) (eisFace π m e₂ D₂ N σ) := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  obtain ⟨h₁, e₁, d₁⟩ := p
  rw [mem_mixedFrames_iff] at hp
  dsimp only at hp ⊢
  obtain ⟨-, -, -, -, -, hk₁, hnE⟩ := hp
  rw [Set.disjoint_left]
  rintro c ⟨hF, ⟨ψ, hψm, hψi, hψd, -, hres⟩, -⟩ ⟨hF', ⟨ζ, hζ0, hres'⟩, -⟩
  obtain ⟨hh, he⟩ := minFaceAt_unique hF hF'
  subst hh
  subst he
  have hψeq : ψ = Polynomial.X - Polynomial.C ζ :=
    monic_irreducible_pow_eq hψm hψi (Polynomial.monic_X_sub_C ζ)
      (Polynomial.irreducible_X_sub_C ζ) (by omega : 1 ≤ m / (e₁ * d₁))
      (hres.symm.trans hres')
  have hd1 : d₁ = 1 := by
    rw [← hψd, hψeq, Polynomial.natDegree_X_sub_C]
  exact hnE ⟨rfl, hd1⟩

/-- ★★ **THE EXACT TILING**: the non-Eisenstein remainder carrier IS the union of the
frame carriers over `mixedFrames m`.  Forward: `powerSector_data` + face uniqueness
give canonical `(h, e', d, k, ψ)` with `e'·d·k = m`; at `(h, d) = (1, 1)` the class
would sit in the `e'`-divisor Eisenstein face (contradiction), so the frame is in
`mixedFrames m`.  Backward: the subset lemma + the Eisenstein-face exclusion. -/
theorem remainder_eq_biUnion {π : O} (hπ : Irreducible π) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) :
    powerSectorFull O π m σ M
        \ ⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
            eisFace π m e' (m / e') (M + m) σ
      = ⋃ p ∈ mixedFrames m,
          mixedFace π m p.1 p.2.1 p.2.2 (M + m) σ := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  ext c
  constructor
  · rintro ⟨⟨hps, h₀, e₀, hF₀, hfull₀⟩, hnot⟩
    obtain ⟨h, e', k, ψ, hF, he'2, hψm, hψirr, hψ0, hk, heq, hd1, hle⟩ :=
      powerSector_data σ hπ hps
    obtain ⟨hh, he⟩ := minFaceAt_unique hF hF₀
    subst hh
    subst he
    have hdec : DecidedAt O m σ (M + m) c := hps.1.1.1.1
    rw [heq, Polynomial.natDegree_pow] at hfull₀
    have hedpos : 0 < e' * ψ.natDegree := Nat.mul_pos (by omega) (by omega)
    have hm' : e' * ψ.natDegree * k = m := by rw [← hfull₀]; ring
    have hm0 : 0 < m := by
      rw [← hm']
      exact Nat.mul_pos hedpos (by omega)
    have hkdiv : m / (e' * ψ.natDegree) = k := by
      rw [← hm']
      exact Nat.mul_div_cancel_left k hedpos
    by_cases hEis : h = 1 ∧ ψ.natDegree = 1
    · -- the Eisenstein frame would sit in a divisor face — contradiction
      exfalso
      obtain ⟨hh1, hdd1⟩ := hEis
      subst hh1
      rw [hdd1] at hm'
      have hek : e' * k = m := by rw [← hm']; ring
      have hke : m / e' = k := by
        rw [← hek]
        exact Nat.mul_div_cancel_left k (by omega : 0 < e')
      obtain ⟨aψ, haψ⟩ : ∃ a, ψ = Polynomial.X + Polynomial.C a :=
        ⟨ψ.coeff 0, hψm.eq_X_add_C hdd1⟩
      have haψ0 : aψ ≠ 0 := by
        intro h0
        apply hψ0
        rw [haψ, h0]
        simp
      have hres2 : classResidualPoly π c 1 e'
          = (Polynomial.X - Polynomial.C (-aψ)) ^ (m / e') := by
        rw [heq, hke]
        congr 1
        rw [haψ, map_neg, sub_neg_eq_add]
      have hmem : e' ∈ (m.divisors.filter fun e'' => 2 ≤ e'' ∧ 2 ≤ m / e'') := by
        rw [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨⟨k, hek.symm⟩, by omega⟩, he'2, ?_⟩
        rw [hke]
        exact hk
      exact hnot (Set.mem_biUnion hmem
        ⟨hF, ⟨-aψ, neg_ne_zero.mpr haψ0, hres2⟩, hdec⟩)
    · -- the mixed frame
      have hmemF : c ∈ mixedFace π m h e' ψ.natDegree (M + m) σ :=
        ⟨hF, ⟨ψ, hψm, hψirr, rfl, hψ0, by rw [heq, hkdiv]⟩, hdec⟩
      have hframe : (h, e', ψ.natDegree) ∈ mixedFrames m := by
        rw [mem_mixedFrames_iff]
        exact ⟨hF.1, hF.2.1, hF.2.2.1, hd1, ⟨k, hm'.symm⟩,
          show 2 ≤ m / (e' * ψ.natDegree) by rw [hkdiv]; exact hk,
          show ¬(h = 1 ∧ ψ.natDegree = 1) from hEis⟩
      exact Set.mem_biUnion hframe hmemF
  · intro hc
    rw [Set.mem_iUnion₂] at hc
    obtain ⟨p, hp, hcp⟩ := hc
    refine ⟨?_, ?_⟩
    · have hp' := mem_mixedFrames_iff.mp hp
      obtain ⟨h₁, e₁, d₁⟩ := p
      dsimp only at hp' hcp
      obtain ⟨hh1, hhe, hcop, hd1, hdvd, hk2, -⟩ := hp'
      exact mixedFace_subset_psf hπ hh1 hhe hd1 hdvd hk2 σ M hcp
    · intro hmem
      rw [Set.mem_iUnion₂] at hmem
      obtain ⟨e₂, he₂, hce⟩ := hmem
      exact Set.disjoint_left.mp (mixedFace_disjoint_eisFace hp σ) hcp hce

/-- ★★ **THE PARTITION COUNT**: the remainder count is the exact frame sum, at every
level. -/
theorem card_remainder_partition {π : O} (hπ : Irreducible π) (m : ℕ)
    (σ : FactorizationType) (M : ℕ) :
    Nat.card ((powerSectorFull O π m σ M
        \ ⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
            eisFace π m e' (m / e') (M + m) σ) : Set (Coeff O m (M + m)))
      = ∑ p ∈ mixedFrames m,
          Nat.card (mixedFace π m p.1 p.2.1 p.2.2 (M + m) σ) := by
  rw [remainder_eq_biUnion hπ m σ M, Nat.card_coe_set_eq,
    ncard_biUnion_eq _ _ (fun p hp p' hp' hne => mixedFace_disjoint hp hp' hne σ)]
  exact Finset.sum_congr rfl fun p _ => (Nat.card_coe_set_eq _).symm

end EisFence

/-! ## §3 — the fires: the row-2 reduction, and the unconditional axes -/

section Fire

/-- ★★★ **THE ROW-2 REDUCTION FIRE**: `EisFullSpanRemainderLaw m σ` from the finitely
many per-frame laws `MixedFaceLaw m h e' d σ`, `(h, e', d) ∈ mixedFrames m` — the
census master's row 2 re-based onto its exact per-axis content.  (`ZcURLim_sum` over
the frame index + the exact partition count.) -/
theorem eisFullSpanRemainderLaw_of_mixedFaceLaws (m : ℕ) (σ : FactorizationType)
    (hlaws : ∀ p ∈ mixedFrames m, MixedFaceLaw m p.1 p.2.1 p.2.2 σ) :
    EisFullSpanRemainderLaw m σ := by
  refine (ZcURLim_sum (mixedFrames m)
    (fun p => fun O _ _ _ _ _ π M =>
      (Nat.card (mixedFace π m p.1 p.2.1 p.2.2 (M + m) σ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))) hlaws).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (∑ p ∈ mixedFrames m,
      (Nat.card (mixedFace π m p.1 p.2.1 p.2.2 (M + m) σ) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))
    = (Nat.card ((powerSectorFull O π m σ M
        \ ⋃ e' ∈ (m.divisors.filter fun e' => 2 ≤ e' ∧ 2 ≤ m / e'),
            eisFace π m e' (m / e') (M + m) σ) : Set (Coeff O m (M + m))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [card_remainder_partition hπ m σ M]
  push_cast
  rw [Finset.sum_div]

/-- ★ **The off-degree axis is UNCONDITIONAL**: at `σ.degree ≠ m` every frame carrier
is empty (a decided class types its lifts at degree `m`). -/
theorem mixedFaceLaw_of_off_degree {m h e' d : ℕ} {σ : FactorizationType}
    (hσ : σ.degree ≠ m) : MixedFaceLaw m h e' d σ := by
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  have hempty : mixedFace π m h e' d (M + m) σ = ∅ := by
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, -, hdec⟩
    obtain ⟨a, ha⟩ := proj_surjective O m (M + m) c
    have hty := hdec a ha
    apply hσ
    rw [← hty, typeOf_degree (monicPoly_monic a), monicPoly_natDegree]
  show (0 : ℝ) = _
  rw [hempty]
  simp

/-- ★ **Row 2 off the degree is UNCONDITIONAL** (the reduction consumed at the empty
axes). -/
theorem eisFullSpanRemainderLaw_of_off_degree {m : ℕ} {σ : FactorizationType}
    (hσ : σ.degree ≠ m) : EisFullSpanRemainderLaw m σ :=
  eisFullSpanRemainderLaw_of_mixedFaceLaws m σ
    (fun _ _ => mixedFaceLaw_of_off_degree hσ)

/-- **Sanity crosscheck**: the reduction independently re-derives IFCG51's `m = 4`
unconditional remainder law from the kernel-decided empty frame census. -/
theorem eisFullSpanRemainderLaw_four_via_frames (σ : FactorizationType) :
    EisFullSpanRemainderLaw 4 σ :=
  eisFullSpanRemainderLaw_of_mixedFaceLaws 4 σ (fun p hp => by
    rw [mixedFrames_four] at hp
    exact absurd hp (Finset.notMem_empty p))

end Fire

/-! ## §4 — THE MIXED LATTICE (charge item 1): the coordinate lattice over the
compositum, by composing the two stage lattices -/

section MixedLattice

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- ★ **The unramified-stage coefficient read**: for `B` of degree `< deg φ` (`φ`
monic), the image of `π^t` divides `mk φ B` iff `π^t` divides EVERY coefficient of
`B` — the `O₁`-valuation of a power-basis vector is the min of the base coefficient
valuations (IFCG27's unramified stage, polynomial form; instance-free). -/
private theorem degree_modByMonicHom_lt' {φ : Polynomial O} (hφ : φ.Monic)
    (x : AdjoinRoot φ) :
    (AdjoinRoot.modByMonicHom hφ x).degree < φ.degree := by
  obtain ⟨Q, hQ⟩ := AdjoinRoot.mk_surjective x
  rw [← hQ, AdjoinRoot.modByMonicHom_mk]
  exact Polynomial.degree_modByMonic_lt Q hφ

theorem unram_pow_dvd_mk_iff {φ : Polynomial O} (hmo : φ.Monic)
    {π : O} {B : Polynomial O} (hB : B.degree < (φ.natDegree : ℕ)) (t : ℕ) :
    (algebraMap O (AdjoinRoot φ) π) ^ t ∣ AdjoinRoot.mk φ B
      ↔ ∀ j < φ.natDegree, π ^ t ∣ B.coeff j := by
  have hφdeg : φ.degree = (φ.natDegree : ℕ) :=
    Polynomial.degree_eq_natDegree hmo.ne_zero
  constructor
  · rintro ⟨y, hy⟩
    set Q : Polynomial O := AdjoinRoot.modByMonicHom hmo y with hQdef
    have hQmk : AdjoinRoot.mk φ Q = y := AdjoinRoot.mk_leftInverse hmo y
    have hQdeg : Q.degree < φ.degree := degree_modByMonicHom_lt' hmo y
    have hmk0 : AdjoinRoot.mk φ (B - Polynomial.C (π ^ t) * Q) = 0 := by
      rw [map_sub, map_mul, hQmk, AdjoinRoot.mk_C, map_pow, hy,
        AdjoinRoot.algebraMap_eq, sub_self]
    have hdvd : φ ∣ B - Polynomial.C (π ^ t) * Q := AdjoinRoot.mk_eq_zero.mp hmk0
    have hzero : B - Polynomial.C (π ^ t) * Q = 0 := by
      by_contra hne
      have h1 : φ.degree ≤ (B - Polynomial.C (π ^ t) * Q).degree :=
        Polynomial.degree_le_of_dvd hdvd hne
      have hBlt : B.degree < φ.degree := by rw [hφdeg]; exact hB
      have hCQ : (Polynomial.C (π ^ t) * Q).degree < φ.degree := by
        rw [← Polynomial.smul_eq_C_mul]
        exact lt_of_le_of_lt (Polynomial.degree_smul_le _ _) hQdeg
      have h2 : (B - Polynomial.C (π ^ t) * Q).degree < φ.degree :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hBlt hCQ)
      exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
    have hBeq : B = Polynomial.C (π ^ t) * Q := sub_eq_zero.mp hzero
    intro j hj
    rw [hBeq, Polynomial.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro hall
    have hdvd : Polynomial.C (π ^ t) ∣ B := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro j
      rcases Nat.lt_or_ge j φ.natDegree with hj | hj
      · exact hall j hj
      · rw [Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le hB (by exact_mod_cast hj))]
        exact dvd_zero _
    obtain ⟨B', hB'⟩ := hdvd
    refine ⟨AdjoinRoot.mk φ B', ?_⟩
    rw [hB', map_mul, AdjoinRoot.mk_C, map_pow, AdjoinRoot.algebraMap_eq]

variable [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **THE MIXED LATTICE — the composed divisibility ceilings** (charge item 1):
over the compositum `O₂ = AdjoinRoot (eisKey (algebraMap π) c₁ e')` of the
unramified stage `O₁ = AdjoinRoot φ` and the Eisenstein stage, root-power
divisibility of a class `mk P` (`deg P < e'`, coefficients represented by base
bi-polynomials `Bᵢ` of degree `< deg φ`) reads as BASE divisibility ceilings:
`α₂^w ∣ mk P ⟺ π^{⌈(w−i)/e'⌉} ∣ (Bᵢ)ⱼ` for all `i < e'`, `j < deg φ` —
`eis_root_pow_dvd_mk_iff`'s Eisenstein ceiling instantiated at `O₁` composed with
the unramified coefficient read.  This is exactly PSL3's recorded missing
instrument ("the RINGS are landed, their coordinate lattices are not"): the
`(1, d)` coordinate lattice over the compositum, every complete DVR, every key,
every centre, uniform in `q, φ, c₁, e', w`. -/
theorem compositum_root_pow_dvd_mk_iff {φ : Polynomial O} (hφ : IsKey φ)
    {π : O} (hπ : Irreducible π) [IsDomain (AdjoinRoot φ)]
    [IsDiscreteValuationRing (AdjoinRoot φ)]
    {c₁ : AdjoinRoot φ} (hc₁ : IsLocalRing.residue (AdjoinRoot φ) c₁ ≠ 0)
    {e' : ℕ} (he' : 0 < e')
    {P : Polynomial (AdjoinRoot φ)} (hP : P.degree < (e' : ℕ))
    {B : ℕ → Polynomial O}
    (hrep : ∀ i < e', P.coeff i = AdjoinRoot.mk φ (B i))
    (hBdeg : ∀ i < e', (B i).degree < (φ.natDegree : ℕ)) (w : ℕ) :
    (AdjoinRoot.root (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e')) ^ w
        ∣ AdjoinRoot.mk (eisKey (algebraMap O (AdjoinRoot φ) π) c₁ e') P
      ↔ ∀ i < e', ∀ j < φ.natDegree,
          π ^ ((w + e' - 1 - i) / e') ∣ (B i).coeff j := by
  haveI : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hφ
  haveI : Finite (ResidueField (AdjoinRoot φ)) :=
    adjoinRoot_finite_residueField hφ
  have hπ₁ : Irreducible (algebraMap O (AdjoinRoot φ) π) :=
    irreducible_algebraMap_adjoinRoot hφ hπ
  rw [eis_root_pow_dvd_mk_iff hπ₁ hc₁ he' hP w]
  constructor
  · intro H i hi j hj
    have h1 := H i hi
    rw [hrep i hi] at h1
    exact (unram_pow_dvd_mk_iff hφ.monic (hBdeg i hi) _).mp h1 j hj
  · intro H i hi
    rw [hrep i hi]
    exact (unram_pow_dvd_mk_iff hφ.monic (hBdeg i hi) _).mpr
      (fun j hj => H i hi j hj)

end MixedLattice

/-! ## §5 — the general-target digit reading (charge item 2: the mixed faces' box
reading at the base ring) -/

section GeneralTarget

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The coefficient read of the x-frame residual under the side pins at general slope
numerator `h` (private replica of IFCG44 §5's read). -/
private theorem xres_coeff_read_h {π : O} {h e' D : ℕ} {G : Polynomial O}
    (hne : (sideSet (Polynomial.X : Polynomial O) G h e').Nonempty)
    (hmin : sideMin (Polynomial.X : Polynomial O) G h e' hne = 0)
    (hdeg : sideDeg (Polynomial.X : Polynomial O) G h e' hne = D) (j : ℕ) :
    (xres π G h e' hne (h * D)).coeff j
      = if j < D + 1 then digAt π (h * (D - j)) (G.coeff (e' * j)) else 0 := by
  classical
  unfold xres
  rw [hdeg, hmin]
  simp only [zero_add]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range (D + 1)) j
    (fun t => digAt π (h * D - h * t) (G.coeff (e' * t)))]
  have hsub : h * D - h * j = h * (D - j) := by
    rcases Nat.le_total j D with hle | hgt
    · obtain ⟨u, hu⟩ : ∃ u, D = j + u := ⟨D - j, by omega⟩
      subst hu
      rw [Nat.mul_add, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    · have h1 : h * D ≤ h * j := Nat.mul_le_mul (le_refl h) hgt
      have h2 : D - j = 0 := by omega
      rw [h2, Nat.mul_zero]
      omega
  rw [hsub]
  simp [Finset.mem_range]

/-- ★★ **THE GENERAL-TARGET DIGIT READING** (the mixed faces' box reading): at slope
`h/e'` under the side pins (`sideMin = 0`, `sideDeg = D`, height `H₀ = h·D`), the
x-frame residual equals ANY monic degree-`D` target `R` IFF the `D` lattice digits at
heights `h·(D−t)` read `R`'s coefficients.  Subsumes the landed `(h, 1)` criterion
(`R = (X − z̄)^D` — the binomial reading) and supplies the `(h, d)` mixed frames
(`R = ψ^k`); ring-free, every DVR, uniform in `q, h, e', D, R`. -/
theorem xres_eq_iff_digits_target {π : O} {h e' D : ℕ}
    {G : Polynomial O} (hG : G.Monic) (hGdeg : G.natDegree = e' * D)
    (hne : (sideSet (Polynomial.X : Polynomial O) G h e').Nonempty)
    (hmin : sideMin (Polynomial.X : Polynomial O) G h e' hne = 0)
    (hdeg : sideDeg (Polynomial.X : Polynomial O) G h e' hne = D)
    {R : Polynomial (IsLocalRing.ResidueField O)} (hR : R.Monic)
    (hRdeg : R.natDegree = D) :
    xres π G h e' hne (h * D) = R
      ↔ ∀ t, t < D → digAt π (h * (D - t)) (G.coeff (e' * t)) = R.coeff t := by
  have hGtop : G.coeff (e' * D) = 1 := by
    rw [← hGdeg]
    exact hG.coeff_natDegree
  constructor
  · intro heq t ht
    have h1 := congrArg (fun P => Polynomial.coeff P t) heq
    rw [xres_coeff_read_h hne hmin hdeg t] at h1
    rw [if_pos (by omega : t < D + 1)] at h1
    exact h1
  · intro hdig
    refine Polynomial.ext fun j => ?_
    rw [xres_coeff_read_h hne hmin hdeg j]
    rcases Nat.lt_trichotomy j D with hj | hj | hj
    · rw [if_pos (by omega : j < D + 1)]
      exact hdig j hj
    · rw [if_pos (by omega : j < D + 1), hj, Nat.sub_self, Nat.mul_zero, digAt_zero,
        hGtop, map_one, ← hRdeg, hR.coeff_natDegree]
    · rw [if_neg (by omega), eq_comm]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- ★ **THE MIXED-FRAME INSTANCE**: the x-frame residual is `ψ^k` (`ψ` monic of
degree `d`) iff the `k·d` lattice digits at heights `h·(k·d−t)` read `ψ^k`'s
coefficients — the `(h, d)` box reading consumed by the frame carriers. -/
theorem xres_eq_psi_pow_iff_digits {π : O} {h e' k d : ℕ}
    {G : Polynomial O} (hG : G.Monic) (hGdeg : G.natDegree = e' * (k * d))
    (hne : (sideSet (Polynomial.X : Polynomial O) G h e').Nonempty)
    (hmin : sideMin (Polynomial.X : Polynomial O) G h e' hne = 0)
    (hdeg : sideDeg (Polynomial.X : Polynomial O) G h e' hne = k * d)
    {ψ : Polynomial (IsLocalRing.ResidueField O)} (hψ : ψ.Monic)
    (hψdeg : ψ.natDegree = d) :
    xres π G h e' hne (h * (k * d)) = ψ ^ k
      ↔ ∀ t, t < k * d →
          digAt π (h * (k * d - t)) (G.coeff (e' * t)) = (ψ ^ k).coeff t :=
  xres_eq_iff_digits_target hG hGdeg hne hmin hdeg (hψ.pow k)
    (by rw [Polynomial.natDegree_pow, hψdeg, Nat.mul_comm])

end GeneralTarget

/-! ## §6 — the composed `(1, d)` criterion over the compositum (charge item 2's
tower composition) -/

section CompositumCriterion

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **THE COMPOSED `(1, d)` CRITERION** (the tower route around the single-ring
obstruction): for a monic pure block `G₁` over the unramified stage
`O₁ = AdjoinRoot φ`, the BASE-RING composed divisibility ceilings on the
bi-polynomial coordinates `B t i` of its `eisKey`-adic development — i.e. the deep
recentred box over the COMPOSITUM `O₂`, read through the mixed lattice — hold IFF
the `O₁`-digit equations of the recentred `k`-th power hold.  This is
`eis_transfer_digits_iff` INSTANTIATED at the unramified stage (the landed criteria
are DVR-uniform, so the tower costs nothing) composed with
`compositum_root_pow_dvd_mk_iff` at every development slot; with
`xres_eq_pow_iff_digits` at `O₁` and `zcURLim_compositum_value` this is the complete
`(1, d)`-axis instrument set.  Uniform in `q, φ, z₁, e', k`, every complete DVR. -/
theorem compositum_transfer_digits_base
    {φ : Polynomial O} (hφ : IsKey φ) {π : O} (hπ : Irreducible π)
    [IsDomain (AdjoinRoot φ)] [IsDiscreteValuationRing (AdjoinRoot φ)]
    {z₁ : AdjoinRoot φ} (hz₁ : IsLocalRing.residue (AdjoinRoot φ) z₁ ≠ 0)
    {k e' : ℕ} (he' : 2 ≤ e') {G₁ : Polynomial (AdjoinRoot φ)}
    (hG : G₁.Monic) (hGdeg : G₁.natDegree = e' * k)
    (hpure : ∀ j, j < e' * k →
      (algebraMap O (AdjoinRoot φ) π) ^ ((e' * k - j + (e' - 1)) / e') ∣ G₁.coeff j)
    {B : ℕ → ℕ → Polynomial O}
    (hrep : ∀ t < k, ∀ i < e',
      (dev (eisKey (algebraMap O (AdjoinRoot φ) π) (-z₁) e') G₁ t).coeff i
        = AdjoinRoot.mk φ (B t i))
    (hBdeg : ∀ t < k, ∀ i < e', (B t i).degree < (φ.natDegree : ℕ)) :
    (∀ t < k, ∀ i < e', ∀ j < φ.natDegree,
        π ^ ((e' * (k - t) + 1 + e' - 1 - i) / e') ∣ (B t i).coeff j)
      ↔ ∀ t, t < k →
          digAt (algebraMap O (AdjoinRoot φ) π) (k - t) (G₁.coeff (e' * t))
            = (k.choose t : IsLocalRing.ResidueField (AdjoinRoot φ))
                * (- IsLocalRing.residue (AdjoinRoot φ) z₁) ^ (k - t) := by
  haveI : IsAdicComplete (maximalIdeal (AdjoinRoot φ)) (AdjoinRoot φ) :=
    adjoinRoot_isAdicComplete hφ
  haveI : Finite (ResidueField (AdjoinRoot φ)) :=
    adjoinRoot_finite_residueField hφ
  have hπ₁ : Irreducible (algebraMap O (AdjoinRoot φ) π) :=
    irreducible_algebraMap_adjoinRoot hφ hπ
  have hz₁' : IsLocalRing.residue (AdjoinRoot φ) (-z₁) ≠ 0 := by
    rw [map_neg]
    exact neg_ne_zero.mpr hz₁
  have hkeymo : (eisKey (algebraMap O (AdjoinRoot φ) π) (-z₁) e').Monic :=
    eisKey_monic (π := algebraMap O (AdjoinRoot φ) π) (c := -z₁)
      (by omega : 0 < e')
  have hdev : ∀ t : ℕ,
      (dev (eisKey (algebraMap O (AdjoinRoot φ) π) (-z₁) e') G₁ t).degree
        < ((e' : ℕ) : WithBot ℕ) := by
    intro t
    have h1 := degree_dev_lt hkeymo
      (by rw [eisKey_natDegree (by omega : 0 < e')]; omega) G₁ t
    have h2 : (eisKey (algebraMap O (AdjoinRoot φ) π) (-z₁) e').degree
        = ((e' : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hkeymo.ne_zero,
        eisKey_natDegree (by omega : 0 < e')]
    rwa [h2] at h1
  rw [← eis_transfer_digits_iff hπ₁ hz₁ he' hG hGdeg hpure]
  constructor
  · intro H t ht
    exact (compositum_root_pow_dvd_mk_iff hφ hπ hz₁' (by omega : 0 < e')
      (hdev t) (hrep t ht) (hBdeg t ht) (e' * (k - t) + 1)).mpr (H t ht)
  · intro H t ht
    exact (compositum_root_pow_dvd_mk_iff hφ hπ hz₁' (by omega : 0 < e')
      (hdev t) (hrep t ht) (hBdeg t ht) (e' * (k - t) + 1)).mp (H t ht)

end CompositumCriterion

/-! ## §7 — the census wire: the master with row 2 on the per-frame laws -/

section MasterWire

/-- ★★★ **THE CENSUS MASTER, ROW 2 RE-BASED ONTO THE FRAMES**: IFCG60's
`decidedSliceAt_all_of_MASTER'''` with the `EisFullSpanRemainderLaw` premise replaced
by the per-frame laws `MixedFaceLaw m h e' d σ` at `(h, e', d) ∈ mixedFrames m` —
row 2's exact per-axis content, through ★★★
`eisFullSpanRemainderLaw_of_mixedFaceLaws`.  The master now rests on
{`FactorCorrespondenceAt` (THE STAGED CITE), the frame laws (THIS ROW), the two
multi-σ convolution defects, the multi-σ leaf sub-face law}. -/
theorem decidedSliceAt_all_of_MASTER_MIXED
    (hFC : ∀ D : ℕ, 2 ≤ D → FactorCorrespondenceAt D)
    (hMixed : ∀ m : ℕ, 6 ≤ m → ¬ m.Prime →
      (∀ k, k < m → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = m → Witnessed m σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) →
        ∀ p ∈ mixedFrames m, MixedFaceLaw m p.1 p.2.1 p.2.2 σ)
    (hSD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
          SplitConvolutionDefectLaw e σ)
    (hPD : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data →
          PowerConvolutionDefectLaw e σ)
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG60.decidedSliceAt_all_of_MASTER''' hFC
    (fun m h6 hnp hsm σ hσ hwit hram =>
      eisFullSpanRemainderLaw_of_mixedFaceLaws m σ
        (hMixed m h6 hnp hsm σ hσ hwit hram))
    hSD hPD hLeafSub

end MasterWire

end Uniformity.Density.IFCG62

section AxCheck
#print axioms Uniformity.Density.IFCG62.mem_mixedFrames_iff
#print axioms Uniformity.Density.IFCG62.mixedFrames_four
#print axioms Uniformity.Density.IFCG62.mixedFrames_six
#print axioms Uniformity.Density.IFCG62.mixedFrames_eight
#print axioms Uniformity.Density.IFCG62.mixedFace_subset_psf
#print axioms Uniformity.Density.IFCG62.mixedFace_disjoint
#print axioms Uniformity.Density.IFCG62.mixedFace_disjoint_eisFace
#print axioms Uniformity.Density.IFCG62.remainder_eq_biUnion
#print axioms Uniformity.Density.IFCG62.card_remainder_partition
#print axioms Uniformity.Density.IFCG62.eisFullSpanRemainderLaw_of_mixedFaceLaws
#print axioms Uniformity.Density.IFCG62.mixedFaceLaw_of_off_degree
#print axioms Uniformity.Density.IFCG62.eisFullSpanRemainderLaw_of_off_degree
#print axioms Uniformity.Density.IFCG62.eisFullSpanRemainderLaw_four_via_frames
#print axioms Uniformity.Density.IFCG62.unram_pow_dvd_mk_iff
#print axioms Uniformity.Density.IFCG62.compositum_root_pow_dvd_mk_iff
#print axioms Uniformity.Density.IFCG62.xres_eq_iff_digits_target
#print axioms Uniformity.Density.IFCG62.xres_eq_psi_pow_iff_digits
#print axioms Uniformity.Density.IFCG62.compositum_transfer_digits_base
#print axioms Uniformity.Density.IFCG62.decidedSliceAt_all_of_MASTER_MIXED
end AxCheck
