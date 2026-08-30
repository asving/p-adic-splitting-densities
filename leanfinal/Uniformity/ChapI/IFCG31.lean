/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG26
import Uniformity.ChapI.IFCG30

/-!
# Uniformity.ChapI.IFCG31 — [CCA 2026-08-30] the mass-4 remainder carrier: partition,
counts, and the odd-ramification closure of `ConeRemainderLaw 4`

Stage CCA of the cone census (design record `runs/wave-c/verdict_CCA.md`).  CN4 (`IFCG24`)
named the remainder family `ConeRemainderLaw (m, σ)`; CRL (`IFCG26`) closed `m = 3` and
landed the engines (the general-position bridge, the Hensel heart, the stratum forcing,
the unit-width decision).  This file assembles the `m = 4` member:

* **§1 the carrier partition** (Lean-core set identity, the `m = 4` instrument):
  `(stratum ∩ shallow) \ pureFaceSet` at `m = 4` is EXACTLY three boxes —
  `box31a = {v₀ ≥ 2, v₁ = 1, v₂ ≥ 1, v₃ ≥ 1}`, `box31b = {v₀ ≥ 3, v₁ = 2, v₂ ≥ 2, v₃ ≥ 1}`
  (the decided sector), and `forcedBox = {v₁ ≥ 2} ∩ ({v₀ = 2} ∪ {v₀ ≥ 3, v₂ = 1})`
  (the even-ramification sector).
* **§2 ★★ the decision** (`decidedAt_quartic_31`): every `box31a/b` class is DECIDED with
  type `{(1,1),(3,1)}` — ONE mechanism, uniformly over the invisible corner (`v₀ = K`,
  `a₀ = 0` included): the class polygon has the two-point side `[1,4]` of slope `v₁/3`,
  the Hensel heart splits off a `(v₁,3)`-pure cubic block (irreducible, `(3,1)`), and the
  leftover is monic linear (`(1,1)`).  NO width pigeonhole and NO X-strip is needed: the
  side `[1, 4]` never touches the corner.
* **§3 ★ the forcing** (`forces_even_ram_of_forced`): every `forcedBox` class carries a
  VISIBLE class face of slope `1/2` (`[0,4]` at `v₀ = 2`; `[2,4]` at `v₂ = 1`), so
  `fracFaceForcesRam_of_stratum` puts a factor with `2 ∣ ramIndexOf` in EVERY lift —
  hence NO type all of whose ramification indices are odd is ever decided there.
* **§4 the exact count**: `coneRemainderCount 4 {(1,1),(3,1)} = (q−1)q^(4K−6) + (q−1)q^(4K−9)`
  at every level `K = M + 4`, and `coneRemainderCount 4 σ = 0` for every OTHER σ with all
  ramification indices odd.
* **§5 ★★★ the laws**: `ConeRemainderLaw 4 ⟨{(1,1),(3,1)}⟩` holds with the constant value
  `(q−1)/q⁶ + (q−1)/q⁹ = (q−1)(q³+1)/q⁹`; `ConeRemainderLaw 4 σ` holds for EVERY σ with
  no even ramification index (`coneRemainderLaw_four_of_odd` — this covers the five
  unramified types and `{(1,1),(3,1)}`, i.e. 6 of the 11 degree-4 types).
* **§6 ★★★ the census front**: `decidedSliceAt_all_of_remainder5_even4_bridge` — the
  all-degree decided slice now rests on the remainder laws at `e ≥ 5`, the `e = 4` laws
  at the EVEN-RAMIFICATION types only (exactly `{(1,1),(1,1),(2,1)}`, `{(1,2),(2,1)}`,
  `{(2,1),(2,1)}`, `{(2,2)}`, `{(4,1)}`), and the block bridges.

## Axiom fence

§1 (carrier, boxes, counts of boxes) is Lean core.  §§2–6 consume exactly ONE extra
axiom, inherited through IFCG26's heart/forcing: the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42).  The C.33 (r = 1) cites are
NOT consumed; no ChapC import.  Zero sorries at landing.

## The honest fence (what stays open at `m = 4`)

The `forcedBox` sector is the genuine residual-refinement territory: its hull genres are
the slope-`1/2` wide faces (residual quadratics — split residuals refine by IFCG30 §4,
irreducible residuals are B.63-leaf territory, double roots recurse) and the `v₂ = 1`
mixed systems.  Its per-type counts are NOT closed here (the depth-0 split/inert residual
counts are parity-structured; the uniform-in-`q` law needs the recursion) — the exact
surviving `e = 4` obligation is the five even-ramification types named above.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG31

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG17 (decidedAt_unique)
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport classNPSupport_le
  le_classCoeffVal_iff_dvd)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_qmonomial shallowSet
  mem_stratum_X_pow_iff card_setOf_le_resOrd card_setOf_resOrd_eq card_pi_set
  faceH faceBox pureFaceSet coneRemainderCount ConeRemainderLaw ZeroConeClause
  zeroConeClause_of_remainderLaw npHeight_coe)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains
  exists_pure_factor_of_two_point_side fracFaceForcesRam_of_stratum
  dvd_natDegree_of_isPure irreducible_of_isPure_natDegree_eq monicFactors_of_irreducible
  monicPoly_zero' mem_sideSet_of_onSide)
open Uniformity.Density.IFCG30 (wideFace_refinement_of_stratum)

attribute [local instance] Classical.propDecidable

/-! ## §0 — the target type and the assembly helper -/

section Supply

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- The mass-4 mixed type of the decided sector: one split linear factor, one totally
ramified cubic. -/
def mixedType4 : FactorizationType := ⟨{(1, 1), (3, 1)}⟩

/-- Shared tail: a monic quartic split as (irreducible `(3,1)`-cubic) × (monic linear)
has type `mixedType4`. -/
private theorem typeOf_eq_of_split_three_one {f F R : Polynomial O}
    (hF : F.Monic) (hR : R.Monic) (hFirr : Irreducible F) (hFe : efPair F = (3, 1))
    (hRd : R.natDegree = 1) (heq : f = F * R) :
    typeOf f = mixedType4 := by
  have hRirr : Irreducible R := irreducible_of_monic_natDegree_one hR hRd
  have hdata : (typeOf f).data = ({(1, 1), (3, 1)} : Multiset (ℕ × ℕ)) := by
    rw [typeOf_data, heq, monicFactors_mul hF hR, monicFactors_of_irreducible hF hFirr,
      monicFactors_of_irreducible hR hRirr, Multiset.map_add, Multiset.map_singleton,
      Multiset.map_singleton, hFe, efPair_of_natDegree_one hR hRd]
    decide
  calc typeOf f = ⟨(typeOf f).data⟩ := rfl
    _ = ⟨({(1, 1), (3, 1)} : Multiset (ℕ × ℕ))⟩ := by rw [hdata]
    _ = mixedType4 := rfl

end Supply

/-! ## §1 — the three boxes and the carrier partition -/

section Carrier

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The first decided box: `v₀ ≥ 2, v₁ = 1, v₂ ≥ 1, v₃ ≥ 1` (pi-set shape). -/
def box31a (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : ℕ) : Set (Coeff O 4 K) :=
  {c | ∀ i : Fin 4,
    c i ∈ (if (i : ℕ) = 0 then {x : Res O K | 2 ≤ resOrd x}
      else if (i : ℕ) = 1 then {x : Res O K | resOrd x = 1}
      else {x : Res O K | 1 ≤ resOrd x})}

/-- The second decided box: `v₀ ≥ 3, v₁ = 2, v₂ ≥ 2, v₃ ≥ 1` (pi-set shape). -/
def box31b (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : ℕ) : Set (Coeff O 4 K) :=
  {c | ∀ i : Fin 4,
    c i ∈ (if (i : ℕ) = 0 then {x : Res O K | 3 ≤ resOrd x}
      else if (i : ℕ) = 1 then {x : Res O K | resOrd x = 2}
      else if (i : ℕ) = 2 then {x : Res O K | 2 ≤ resOrd x}
      else {x : Res O K | 1 ≤ resOrd x})}

/-- The even-ramification (forced) sector: `v₁ ≥ 2` with `v₀ = 2`, or
`v₀ ≥ 3, v₁ ≥ 2, v₂ = 1` — every class here carries a visible slope-`1/2` face. -/
def forcedBox (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : ℕ) : Set (Coeff O 4 K) :=
  {c | 1 ≤ resOrd (c 3) ∧ 1 ≤ resOrd (c 2) ∧
    ((resOrd (c 0) = 2 ∧ 2 ≤ resOrd (c 1))
      ∨ (3 ≤ resOrd (c 0) ∧ 2 ≤ resOrd (c 1) ∧ resOrd (c 2) = 1))}

theorem mem_box31a_iff {K : ℕ} (c : Coeff O 4 K) :
    c ∈ box31a O K ↔
      2 ≤ resOrd (c 0) ∧ resOrd (c 1) = 1 ∧ 1 ≤ resOrd (c 2) ∧ 1 ≤ resOrd (c 3) := by
  constructor
  · intro hc
    have h0' := hc 0
    have h1' := hc 1
    have h2' := hc 2
    have h3' := hc 3
    rw [if_pos (show ((0 : Fin 4) : ℕ) = 0 from rfl)] at h0'
    rw [if_neg (show ¬ ((1 : Fin 4) : ℕ) = 0 by decide),
      if_pos (show ((1 : Fin 4) : ℕ) = 1 from rfl)] at h1'
    rw [if_neg (show ¬ ((2 : Fin 4) : ℕ) = 0 by decide),
      if_neg (show ¬ ((2 : Fin 4) : ℕ) = 1 by decide)] at h2'
    rw [if_neg (show ¬ ((3 : Fin 4) : ℕ) = 0 by decide),
      if_neg (show ¬ ((3 : Fin 4) : ℕ) = 1 by decide)] at h3'
    exact ⟨h0', h1', h2', h3'⟩
  · rintro ⟨hA, hB, hC, hD⟩ i
    by_cases hi0 : (i : ℕ) = 0
    · rw [if_pos hi0, show i = 0 from Fin.ext hi0]
      exact hA
    · rw [if_neg hi0]
      by_cases hi1 : (i : ℕ) = 1
      · rw [if_pos hi1, show i = 1 from Fin.ext hi1]
        exact hB
      · rw [if_neg hi1]
        by_cases hi2 : (i : ℕ) = 2
        · rw [show i = 2 from Fin.ext hi2]
          exact hC
        · have hieq : i = 3 := by
            have h5 := i.isLt
            exact Fin.ext (by omega)
          rw [hieq]
          exact hD

theorem mem_box31b_iff {K : ℕ} (c : Coeff O 4 K) :
    c ∈ box31b O K ↔
      3 ≤ resOrd (c 0) ∧ resOrd (c 1) = 2 ∧ 2 ≤ resOrd (c 2) ∧ 1 ≤ resOrd (c 3) := by
  constructor
  · intro hc
    have h0' := hc 0
    have h1' := hc 1
    have h2' := hc 2
    have h3' := hc 3
    rw [if_pos (show ((0 : Fin 4) : ℕ) = 0 from rfl)] at h0'
    rw [if_neg (show ¬ ((1 : Fin 4) : ℕ) = 0 by decide),
      if_pos (show ((1 : Fin 4) : ℕ) = 1 from rfl)] at h1'
    rw [if_neg (show ¬ ((2 : Fin 4) : ℕ) = 0 by decide),
      if_neg (show ¬ ((2 : Fin 4) : ℕ) = 1 by decide),
      if_pos (show ((2 : Fin 4) : ℕ) = 2 from rfl)] at h2'
    rw [if_neg (show ¬ ((3 : Fin 4) : ℕ) = 0 by decide),
      if_neg (show ¬ ((3 : Fin 4) : ℕ) = 1 by decide),
      if_neg (show ¬ ((3 : Fin 4) : ℕ) = 2 by decide)] at h3'
    exact ⟨h0', h1', h2', h3'⟩
  · rintro ⟨hA, hB, hC, hD⟩ i
    by_cases hi0 : (i : ℕ) = 0
    · rw [if_pos hi0, show i = 0 from Fin.ext hi0]
      exact hA
    · rw [if_neg hi0]
      by_cases hi1 : (i : ℕ) = 1
      · rw [if_pos hi1, show i = 1 from Fin.ext hi1]
        exact hB
      · rw [if_neg hi1]
        by_cases hi2 : (i : ℕ) = 2
        · rw [if_pos hi2, show i = 2 from Fin.ext hi2]
          exact hC
        · rw [if_neg hi2]
          have hieq : i = 3 := by
            have h5 := i.isLt
            exact Fin.ext (by omega)
          rw [hieq]
          exact hD

/-- ★ **The mass-4 remainder carrier** (the `m = 4` instrument): outside the two pure-face
boxes (`h ∈ {1, 3}`), the shallow stratum is EXACTLY the two decided boxes plus the
even-ramification sector. -/
theorem remainder_carrier_four {K : ℕ} (hK : 4 ≤ K) :
    ((levelZeroStratum O 4 K (X ^ 4) ∩ shallowSet O 4 K) \ pureFaceSet O 4 K)
      = (box31a O K ∪ box31b O K) ∪ forcedBox O K := by
  have hK1 : 1 ≤ K := by omega
  ext c
  have e0 : npHeight c 0 = resOrd (c 0) := by simpa using npHeight_coe c (0 : Fin 4)
  have e1 : npHeight c 1 = resOrd (c 1) := by simpa using npHeight_coe c (1 : Fin 4)
  have e2 : npHeight c 2 = resOrd (c 2) := by simpa using npHeight_coe c (2 : Fin 4)
  have e3 : npHeight c 3 = resOrd (c 3) := by simpa using npHeight_coe c (3 : Fin 4)
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, mem_box31a_iff,
    mem_box31b_iff, forcedBox, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hstr, hsh⟩, hnb⟩
    have hstr' := (mem_stratum_X_pow_iff hK1 c).1 hstr
    have hv0 : 1 ≤ resOrd (c 0) := hstr' 0
    have hv1 : 1 ≤ resOrd (c 1) := hstr' 1
    have hv2 : 1 ≤ resOrd (c 2) := hstr' 2
    have hv3 : 1 ≤ resOrd (c 3) := hstr' 3
    have hshallow : resOrd (c 0) < 4 ∨ resOrd (c 1) < 3 ∨ resOrd (c 2) < 2 := by
      obtain ⟨i, hi⟩ := hsh
      fin_cases i
      · exact Or.inl (by have hi' : resOrd (c 0) < 4 - 0 := hi; omega)
      · exact Or.inr (Or.inl (by have hi' : resOrd (c 1) < 4 - 1 := hi; omega))
      · exact Or.inr (Or.inr (by have hi' : resOrd (c 2) < 4 - 2 := hi; omega))
      · exfalso
        have hi' : resOrd (c 3) < 4 - 3 := hi
        omega
    have hne1 : resOrd (c 0) ≠ 1 := by
      intro hv0eq
      refine hnb ⟨1, ?_, ?_, ?_⟩
      · show (1 : ℕ) ∈ faceH 4
        simp only [faceH, Finset.mem_filter, Finset.mem_range]
        exact ⟨by norm_num, by norm_num, Nat.coprime_one_left 4⟩
      · rw [e0]
        exact hv0eq
      · intro i
        fin_cases i
        · exact (show 1 * (4 - 0) ≤ 4 * npHeight c 0 by rw [e0]; omega)
        · exact (show 1 * (4 - 1) ≤ 4 * npHeight c 1 by rw [e1]; omega)
        · exact (show 1 * (4 - 2) ≤ 4 * npHeight c 2 by rw [e2]; omega)
        · exact (show 1 * (4 - 3) ≤ 4 * npHeight c 3 by rw [e3]; omega)
    have hnot3 : ¬ (resOrd (c 0) = 3 ∧ 3 ≤ resOrd (c 1) ∧ 2 ≤ resOrd (c 2)) := by
      rintro ⟨hv0eq, hv1ge, hv2ge⟩
      refine hnb ⟨3, ?_, ?_, ?_⟩
      · show (3 : ℕ) ∈ faceH 4
        simp only [faceH, Finset.mem_filter, Finset.mem_range]
        exact ⟨by norm_num, by norm_num, by decide⟩
      · rw [e0]
        exact hv0eq
      · intro i
        fin_cases i
        · exact (show 3 * (4 - 0) ≤ 4 * npHeight c 0 by rw [e0]; omega)
        · exact (show 3 * (4 - 1) ≤ 4 * npHeight c 1 by rw [e1]; omega)
        · exact (show 3 * (4 - 2) ≤ 4 * npHeight c 2 by rw [e2]; omega)
        · exact (show 3 * (4 - 3) ≤ 4 * npHeight c 3 by rw [e3]; omega)
    omega
  · intro hc
    have hv0 : 1 ≤ resOrd (c 0) := by omega
    have hv1 : 1 ≤ resOrd (c 1) := by omega
    have hv2 : 1 ≤ resOrd (c 2) := by omega
    have hv3 : 1 ≤ resOrd (c 3) := by omega
    have hshallow : resOrd (c 0) < 4 ∨ resOrd (c 1) < 3 ∨ resOrd (c 2) < 2 := by omega
    have hne1 : resOrd (c 0) ≠ 1 := by omega
    have hnot3 : ¬ (resOrd (c 0) = 3 ∧ 3 ≤ resOrd (c 1) ∧ 2 ≤ resOrd (c 2)) := by omega
    have hstr : ∀ i : Fin 4, 1 ≤ resOrd (c i) := by
      intro i
      fin_cases i
      · exact hv0
      · exact hv1
      · exact hv2
      · exact hv3
    refine ⟨⟨(mem_stratum_X_pow_iff hK1 c).2 hstr, ?_⟩, ?_⟩
    · rcases hshallow with h5 | h5 | h5
      · exact ⟨0, show resOrd (c 0) < 4 - 0 by omega⟩
      · exact ⟨1, show resOrd (c 1) < 4 - 1 by omega⟩
      · exact ⟨2, show resOrd (c 2) < 4 - 2 by omega⟩
    · rintro ⟨h, hh, hc0, hcond⟩
      have hh5 : h < 4 ∧ (1 ≤ h ∧ Nat.Coprime h 4) := by
        have h5 := hh
        simp only [faceH, Finset.mem_filter, Finset.mem_range] at h5
        exact h5
      rw [e0] at hc0
      have hcond1 : h * (4 - 1) ≤ 4 * npHeight c 1 := hcond 1
      have hcond2 : h * (4 - 2) ≤ 4 * npHeight c 2 := hcond 2
      rw [e1] at hcond1
      rw [e2] at hcond2
      have hh' : h = 1 ∨ h = 2 ∨ h = 3 := by omega
      rcases hh' with rfl | rfl | rfl
      · omega
      · exact absurd hh5.2.2 (by decide)
      · exact hnot3 ⟨hc0, by omega, by omega⟩

/-- The first decided box count: `(q−1)·q^(4K−6)`. -/
theorem card_box31a {K : ℕ} (hK : 4 ≤ K) :
    Nat.card (box31a O K : Set (Coeff O 4 K))
      = (residueCard O - 1) * residueCard O ^ (4 * K - 6) := by
  classical
  unfold box31a
  rw [card_pi_set, Fin.prod_univ_four]
  rw [if_pos (show ((0 : Fin 4) : ℕ) = 0 from rfl)]
  rw [if_neg (show ¬ ((1 : Fin 4) : ℕ) = 0 by decide),
    if_pos (show ((1 : Fin 4) : ℕ) = 1 from rfl)]
  rw [if_neg (show ¬ ((2 : Fin 4) : ℕ) = 0 by decide),
    if_neg (show ¬ ((2 : Fin 4) : ℕ) = 1 by decide)]
  rw [if_neg (show ¬ ((3 : Fin 4) : ℕ) = 0 by decide),
    if_neg (show ¬ ((3 : Fin 4) : ℕ) = 1 by decide)]
  rw [card_setOf_le_resOrd (show 2 ≤ K by omega),
    card_setOf_resOrd_eq (show 1 < K by omega),
    card_setOf_le_resOrd (show 1 ≤ K by omega)]
  rw [show K - 1 - 1 = K - 2 from by omega,
    show 4 * K - 6 = (K - 2) + (K - 2) + ((K - 1) + (K - 1)) from by omega,
    pow_add, pow_add, pow_add]
  ring

/-- The second decided box count: `(q−1)·q^(4K−9)`. -/
theorem card_box31b {K : ℕ} (hK : 4 ≤ K) :
    Nat.card (box31b O K : Set (Coeff O 4 K))
      = (residueCard O - 1) * residueCard O ^ (4 * K - 9) := by
  classical
  unfold box31b
  rw [card_pi_set, Fin.prod_univ_four]
  rw [if_pos (show ((0 : Fin 4) : ℕ) = 0 from rfl)]
  rw [if_neg (show ¬ ((1 : Fin 4) : ℕ) = 0 by decide),
    if_pos (show ((1 : Fin 4) : ℕ) = 1 from rfl)]
  rw [if_neg (show ¬ ((2 : Fin 4) : ℕ) = 0 by decide),
    if_neg (show ¬ ((2 : Fin 4) : ℕ) = 1 by decide),
    if_pos (show ((2 : Fin 4) : ℕ) = 2 from rfl)]
  rw [if_neg (show ¬ ((3 : Fin 4) : ℕ) = 0 by decide),
    if_neg (show ¬ ((3 : Fin 4) : ℕ) = 1 by decide),
    if_neg (show ¬ ((3 : Fin 4) : ℕ) = 2 by decide)]
  rw [card_setOf_le_resOrd (show 3 ≤ K by omega),
    card_setOf_resOrd_eq (show 2 < K by omega),
    card_setOf_le_resOrd (show 2 ≤ K by omega),
    card_setOf_le_resOrd (show 1 ≤ K by omega)]
  rw [show K - 2 - 1 = K - 3 from by omega,
    show 4 * K - 9 = (K - 3) + (K - 3) + ((K - 2) + (K - 1)) from by omega,
    pow_add, pow_add, pow_add]
  ring

end Carrier

/-! ## §2 — ★★ the decision: both boxes are decided `{(1,1),(3,1)}` by ONE mechanism -/

section Decision

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **The mass-4 mixed decision**, `t`-parametrized over both boxes (`t = v₁ ∈ {1, 2}`;
`t = 1` is `box31a`, `t = 2` is `box31b`): the class polygon has the two-point side
`[1, 4]` of slope `t/3`, so every lift splits as a `(t,3)`-pure cubic (irreducible,
`efPair (3,1)`) times a monic linear (`(1,1)`) — uniformly over the invisible corner
(`v₀ = K` and `a₀ = 0` included; the side never touches abscissa `0`). -/
theorem decidedAt_quartic_31 {K : ℕ} (hK : 3 ≤ K) {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t ≤ 2)
    {c : Coeff O 4 K} (h0 : t + 1 ≤ classCoeffVal c 0) (h1 : classCoeffVal c 1 = t)
    (h2 : t ≤ classCoeffVal c 2) (h3 : 1 ≤ classCoeffVal c 3) :
    DecidedAt O 4 mixedType4 K c := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hcop : Nat.Coprime t 3 := by interval_cases t <;> decide
  intro a ha
  -- STEP 1: the class polygon at slope data `(t, 3)`: support `4t`, attained at `1, 4`.
  have hnp0 : t + 1 ≤ npHeight c 0 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (0 : ℕ) < 4)]
    exact h0
  have hnp1 : npHeight c 1 = t := by
    unfold npHeight
    rw [dif_pos (by norm_num : (1 : ℕ) < 4)]
    exact h1
  have hnp2 : t ≤ npHeight c 2 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (2 : ℕ) < 4)]
    exact h2
  have hnp3 : 1 ≤ npHeight c 3 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (3 : ℕ) < 4)]
    exact h3
  have hnp4 : npHeight c 4 = 0 := by
    unfold npHeight
    rw [dif_neg (by norm_num : ¬ (4 : ℕ) < 4)]
  have hsup : classNPSupport c t 3 = 4 * t := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h5 := classNPSupport_le_apply c t 3 (show (1 : ℕ) ≤ 4 by norm_num)
      rw [hnp1] at h5
      omega
    · intro i hi
      interval_cases i
      · omega
      · omega
      · omega
      · omega
      · omega
  have hA1 : NPAttains c t 3 1 := ⟨by omega, by rw [hnp1, hsup]; ring⟩
  have hA4 : NPAttains c t 3 4 := ⟨le_refl 4, by rw [hnp4, hsup]; ring⟩
  have hvis : NPVisibleAt c t 3 := by
    show classNPSupport c t 3 < 3 * K
    rw [hsup]
    omega
  -- STEP 2: the bridge — every lift is OnSide at `1` and `4`.
  obtain ⟨hO1, hsupf⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hA1 ha
  obtain ⟨hO4, -⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hA4 ha
  have htop : suppVal X (monicPoly a) t 3 ≠ ⊤ := by
    rw [hsupf]
    exact ENat.coe_ne_top _
  -- STEP 3: the stratum reduction `f̄ = X̄⁴` (all class heights positive).
  have hres : (monicPoly a).map (residue O) = X ^ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree, map_monicPoly]
    have hzero : (fun i => residue O (a i)) = (fun _ : Fin 4 => (0 : ResidueField O)) := by
      funext i
      have h6 : 1 ≤ classCoeffVal c i := by
        fin_cases i
        · exact le_trans (by omega) h0
        · exact le_of_le_of_eq ht1 h1.symm
        · exact le_trans ht1 h2
        · exact h3
      have h7 := (le_classCoeffVal_iff_dvd hπ (by omega : 1 ≤ K) ha i).1 h6
      rw [pow_one] at h7
      exact (IsLocalRing.residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hπ _).2 h7)
    rw [hzero, monicPoly_zero']
  -- STEP 4: the Hensel heart — split off the pure `(t, 3)` factor.
  obtain ⟨F, R, hFm, hRm, hFp, hFd, heqFR⟩ :=
    exists_pure_factor_of_two_point_side hπ (monicPoly_monic a) hres (by omega)
      (by norm_num) hcop (by norm_num : (1 : ℕ) < 4) (monicPoly_natDegree a).ge
      hO1 hO4 htop
  -- STEP 5: degree bookkeeping — the pure block is the cubic, the rest is linear.
  have h3dvd : 3 ∣ F.natDegree :=
    dvd_natDegree_of_isPure hπ hFm (by norm_num) hcop hFp
  have hdegsum : F.natDegree + R.natDegree = 4 := by
    have h6 := monicPoly_natDegree a
    rw [heqFR, Polynomial.natDegree_mul hFm.ne_zero hRm.ne_zero] at h6
    omega
  have hFdeg : F.natDegree = 3 := by omega
  have hRdeg : R.natDegree = 1 := by omega
  -- STEP 6: the unit-width decision + assembly.
  obtain ⟨hFirr, hFef⟩ := irreducible_of_isPure_natDegree_eq hπ hFm (by norm_num)
    hcop hFp hFdeg
  exact typeOf_eq_of_split_three_one hFm hRm hFirr hFef hRdeg heqFR

end Decision

/-! ## §3 — ★ the forcing: the forced sector always ramifies evenly -/

section Forcing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **The even-ramification forcing**: a `forcedBox`-shaped class carries a visible
class NP face of slope `1/2` (`[0,4]` in the `v₀ = 2` case, `[2,4]` in the `v₂ = 1`
case), so EVERY lift has a monic irreducible factor of even ramification index. -/
theorem forces_even_ram_of_forced {K : ℕ} (hK : 3 ≤ K) {c : Coeff O 4 K}
    (hstr : ∀ i : Fin 4, 1 ≤ classCoeffVal c i)
    (hcase : (classCoeffVal c 0 = 2 ∧ 2 ≤ classCoeffVal c 1)
      ∨ (3 ≤ classCoeffVal c 0 ∧ 2 ≤ classCoeffVal c 1 ∧ classCoeffVal c 2 = 1))
    {a : Fin 4 → O} (ha : proj O 4 K a = c) :
    ∃ g' ∈ monicFactors (monicPoly a), 2 ∣ ramIndexOf g' := by
  have hstr' : c ∈ levelZeroStratum O 4 K (X ^ 4) :=
    (mem_stratum_X_pow_iff (by omega) c).2 hstr
  have hnp1ge : 1 ≤ npHeight c 1 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (1 : ℕ) < 4)]
    exact hstr 1
  have hnp3ge : 1 ≤ npHeight c 3 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (3 : ℕ) < 4)]
    exact hstr 3
  have hnp4 : npHeight c 4 = 0 := by
    unfold npHeight
    rw [dif_neg (by norm_num : ¬ (4 : ℕ) < 4)]
  rcases hcase with ⟨hv0, hv1⟩ | ⟨hv0, hv1, hv2⟩
  · -- the `v₀ = 2` face `[0, 4]` of slope `1/2`
    have hnp0 : npHeight c 0 = 2 := by
      unfold npHeight
      rw [dif_pos (by norm_num : (0 : ℕ) < 4)]
      exact hv0
    have hnp1 : 2 ≤ npHeight c 1 := by
      unfold npHeight
      rw [dif_pos (by norm_num : (1 : ℕ) < 4)]
      exact hv1
    have hnp2 : 1 ≤ npHeight c 2 := by
      unfold npHeight
      rw [dif_pos (by norm_num : (2 : ℕ) < 4)]
      exact hstr 2
    have hsup : classNPSupport c 1 2 = 4 := by
      refine le_antisymm ?_ (le_classNPSupport ?_)
      · have h5 := classNPSupport_le_apply c 1 2 (show (0 : ℕ) ≤ 4 by norm_num)
        rw [hnp0] at h5
        omega
      · intro i hi
        interval_cases i
        · omega
        · omega
        · omega
        · omega
        · omega
    have hface : ClassNPFace c 1 2 :=
      ⟨0, 4, by norm_num, ⟨by omega, by rw [hnp0, hsup]⟩, ⟨le_refl 4, by rw [hnp4, hsup]⟩⟩
    have hvis : NPVisibleAt c 1 2 := by
      show classNPSupport c 1 2 < 2 * K
      rw [hsup]
      omega
    exact fracFaceForcesRam_of_stratum (by norm_num) (Nat.coprime_one_left 2) hstr'
      hface hvis ha
  · -- the `v₂ = 1` face `[2, 4]` of slope `1/2`
    have hnp0 : 3 ≤ npHeight c 0 := by
      unfold npHeight
      rw [dif_pos (by norm_num : (0 : ℕ) < 4)]
      exact hv0
    have hnp1 : 2 ≤ npHeight c 1 := by
      unfold npHeight
      rw [dif_pos (by norm_num : (1 : ℕ) < 4)]
      exact hv1
    have hnp2 : npHeight c 2 = 1 := by
      unfold npHeight
      rw [dif_pos (by norm_num : (2 : ℕ) < 4)]
      exact hv2
    have hsup : classNPSupport c 1 2 = 4 := by
      refine le_antisymm ?_ (le_classNPSupport ?_)
      · have h5 := classNPSupport_le_apply c 1 2 (show (2 : ℕ) ≤ 4 by norm_num)
        rw [hnp2] at h5
        omega
      · intro i hi
        interval_cases i
        · omega
        · omega
        · omega
        · omega
        · omega
    have hface : ClassNPFace c 1 2 :=
      ⟨2, 4, by norm_num, ⟨by omega, by rw [hnp2, hsup]⟩, ⟨le_refl 4, by rw [hnp4, hsup]⟩⟩
    have hvis : NPVisibleAt c 1 2 := by
      show classNPSupport c 1 2 < 2 * K
      rw [hsup]
      omega
    exact fracFaceForcesRam_of_stratum (by norm_num) (Nat.coprime_one_left 2) hstr'
      hface hvis ha

/-- The forced-sector data implies the stratum bounds. -/
theorem stratum_of_forced {K : ℕ} {c : Coeff O 4 K}
    (hd3 : 1 ≤ resOrd (c 3)) (hd2 : 1 ≤ resOrd (c 2))
    (hcase : (resOrd (c 0) = 2 ∧ 2 ≤ resOrd (c 1))
      ∨ (3 ≤ resOrd (c 0) ∧ 2 ≤ resOrd (c 1) ∧ resOrd (c 2) = 1)) :
    ∀ i : Fin 4, 1 ≤ classCoeffVal c i := by
  have hv0 : 1 ≤ resOrd (c 0) := by omega
  have hv1 : 1 ≤ resOrd (c 1) := by omega
  intro i
  fin_cases i
  · exact hv0
  · exact hv1
  · exact hd2
  · exact hd3

/-- No all-odd-ramification type is ever decided on the forced sector. -/
theorem not_decidedAt_of_forced_of_odd {K : ℕ} (hK : 3 ≤ K) {c : Coeff O 4 K}
    (hstr : ∀ i : Fin 4, 1 ≤ classCoeffVal c i)
    (hcase : (classCoeffVal c 0 = 2 ∧ 2 ≤ classCoeffVal c 1)
      ∨ (3 ≤ classCoeffVal c 0 ∧ 2 ≤ classCoeffVal c 1 ∧ classCoeffVal c 2 = 1))
    {σ : FactorizationType} (hodd : ∀ p ∈ σ.data, ¬ 2 ∣ p.1) :
    ¬ DecidedAt O 4 σ K c := by
  intro hdec
  obtain ⟨a, ha⟩ := proj_surjective O 4 K c
  obtain ⟨g', hg', h2dvd⟩ := forces_even_ram_of_forced hK hstr hcase ha
  have hmem : efPair g' ∈ (typeOf (monicPoly a)).data := by
    rw [typeOf_data]
    exact Multiset.mem_map_of_mem _ hg'
  rw [hdec a ha] at hmem
  exact hodd _ hmem h2dvd

end Forcing

/-! ## §3b — the sector-(b) demo: the wide-face SPLIT-residual leaf is DECIDED

The forced sector is the honest fence; this section lands its first decided leaf, the
exact shape the even-ramification successor consumes: an `E1` class (`v₀ = 2`, `v₁ ≥ 2`)
whose slope-`1/2` class residual splits into coprime monic LINEAR factors is decided
`{(2,1),(2,1)}` — IFCG30 §4's refinement fires verbatim, IFCG26 §4 decides both blocks,
and the cofactor `R` is forced to `1` by degrees.  (The irreducible-residual leaf is
B.63 territory; the double-root residual is the recursion's — both stay open.) -/

section SplitLeaf

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The doubly ramified pair type. -/
def ramPairType : FactorizationType := ⟨{(2, 1), (2, 1)}⟩

/-- ★ **The split-residual leaf of the forced sector's `E1` cell**: `v₀ = 2` exact,
`v₁ ≥ 2`, and the class residual of the `[0,4]` slope-`1/2` face (read off the reference
lift `a₀`; class data by IFCG28 §3) splitting into coprime monic linears decides the
class as `{(2,1),(2,1)}`. -/
theorem decidedAt_forced_split {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K}
    (h0 : classCoeffVal c 0 = 2) (h1 : 2 ≤ classCoeffVal c 1)
    (h2 : 1 ≤ classCoeffVal c 2) (h3 : 1 ≤ classCoeffVal c 3)
    {a₀ : Fin 4 → O} (ha₀ : proj O 4 K a₀ = c)
    (hne₀ : (sideSet X (monicPoly a₀) 1 2).Nonempty)
    {G H : Polynomial (resField (X : Polynomial O))}
    (hG : G.Monic) (hH : H.Monic) (hGdeg : G.natDegree = 1) (hHdeg : H.natDegree = 1)
    (hGH : IsCoprime G H)
    (hres : resPoly π X (monicPoly a₀) 1 2 hne₀ 2 = G * H) :
    DecidedAt O 4 ramPairType K c := by
  -- the class face `[0, 4]` of slope `1/2` (the E1 computation)
  have hnp0 : npHeight c 0 = 2 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (0 : ℕ) < 4)]
    exact h0
  have hnp1 : 2 ≤ npHeight c 1 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (1 : ℕ) < 4)]
    exact h1
  have hnp2 : 1 ≤ npHeight c 2 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (2 : ℕ) < 4)]
    exact h2
  have hnp3 : 1 ≤ npHeight c 3 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (3 : ℕ) < 4)]
    exact h3
  have hnp4 : npHeight c 4 = 0 := by
    unfold npHeight
    rw [dif_neg (by norm_num : ¬ (4 : ℕ) < 4)]
  have hsup : classNPSupport c 1 2 = 4 := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h5 := classNPSupport_le_apply c 1 2 (show (0 : ℕ) ≤ 4 by norm_num)
      rw [hnp0] at h5
      omega
    · intro i hi
      interval_cases i
      · omega
      · omega
      · omega
      · omega
      · omega
  have hAt0 : NPAttains c 1 2 0 := ⟨by omega, by rw [hnp0, hsup]⟩
  have hAt4 : NPAttains c 1 2 4 := ⟨le_refl 4, by rw [hnp4, hsup]⟩
  have hface : ClassNPFace c 1 2 := ⟨0, 4, by norm_num, hAt0, hAt4⟩
  have hvis : NPVisibleAt c 1 2 := by
    show classNPSupport c 1 2 < 2 * K
    rw [hsup]
    omega
  have hstr' : c ∈ levelZeroStratum O 4 K (X ^ 4) := by
    refine (mem_stratum_X_pow_iff (by omega) c).2 ?_
    intro i
    fin_cases i
    · exact le_of_le_of_eq (by norm_num) h0.symm
    · exact le_trans (by norm_num) h1
    · exact h2
    · exact h3
  -- the reference lift's side data: `sideMin = 0`, left height `2`
  have hO0 : OnSide X (monicPoly a₀) 1 2 0 :=
    (onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hAt0 ha₀).1
  have h0mem : (0 : ℕ) ∈ sideSet X (monicPoly a₀) 1 2 :=
    mem_sideSet_of_onSide (Nat.zero_le _) hO0
  have hmin0 : sideMin X (monicPoly a₀) 1 2 hne₀ = 0 :=
    Nat.le_zero.mp (Finset.min'_le _ 0 h0mem)
  have hH0 : npHgt X (monicPoly a₀) (sideMin X (monicPoly a₀) 1 2 hne₀)
      = ((2 : ℕ) : ℕ∞) := by
    rw [hmin0, npHgt_monicPoly_eq hπ ha₀ (by norm_num : (0 : ℕ) < 4)
      (lt_of_eq_of_lt h0 (by omega))]
    exact Nat.cast_inj.mpr h0
  -- the refinement fires on every lift
  intro a ha
  obtain ⟨g, h', R, hgm, hhm, hRm, heq, hgdeg, hhdeg, hgp, hhp, -, -, -, -⟩ :=
    wideFace_refinement_of_stratum hπ (by norm_num) one_pos two_pos
      (Nat.coprime_one_left 2) hstr' (lt_of_eq_of_lt h0 (by omega)) hface hvis ha₀
      hne₀ hH0 hG hH hGH hres ha
  have hgd2 : g.natDegree = 2 := by omega
  have hhd2 : h'.natDegree = 2 := by omega
  have hd : g.natDegree + h'.natDegree + R.natDegree = 4 := by
    have h6 := monicPoly_natDegree a
    rw [heq, Polynomial.natDegree_mul (mul_ne_zero hgm.ne_zero hhm.ne_zero) hRm.ne_zero,
      Polynomial.natDegree_mul hgm.ne_zero hhm.ne_zero] at h6
    omega
  have hRdeg : R.natDegree = 0 := by omega
  have hR1 : R = 1 := (Polynomial.Monic.natDegree_eq_zero hRm).mp hRdeg
  have heq2 : monicPoly a = g * h' := by rw [heq, hR1, mul_one]
  obtain ⟨hgirr, hgef⟩ := irreducible_of_isPure_natDegree_eq hπ hgm (by norm_num)
    (Nat.coprime_one_left 2) hgp hgd2
  obtain ⟨hhirr, hhef⟩ := irreducible_of_isPure_natDegree_eq hπ hhm (by norm_num)
    (Nat.coprime_one_left 2) hhp hhd2
  have hdata : (typeOf (monicPoly a)).data = ({(2, 1), (2, 1)} : Multiset (ℕ × ℕ)) := by
    rw [typeOf_data, heq2, monicFactors_mul hgm hhm, monicFactors_of_irreducible hgm hgirr,
      monicFactors_of_irreducible hhm hhirr, Multiset.map_add, Multiset.map_singleton,
      Multiset.map_singleton, hgef, hhef]
    rfl
  calc typeOf (monicPoly a) = ⟨(typeOf (monicPoly a)).data⟩ := rfl
    _ = ⟨({(2, 1), (2, 1)} : Multiset (ℕ × ℕ))⟩ := by rw [hdata]
    _ = ramPairType := rfl

end SplitLeaf

/-! ## §4 — the exact mass-4 remainder counts at the odd-ramification types -/

section Count

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **The mass-4 remainder count at the mixed type** — two exact monomials, every
finite level. -/
theorem coneRemainderCount_four_mixed (M : ℕ) :
    coneRemainderCount O 4 mixedType4 M
      = (residueCard O - 1) * residueCard O ^ (4 * (M + 4) - 6)
        + (residueCard O - 1) * residueCard O ^ (4 * (M + 4) - 9) := by
  classical
  unfold coneRemainderCount
  have hK : 4 ≤ M + 4 := by omega
  have hassoc : ((decidedSet O 4 mixedType4 (M + 4)
        ∩ levelZeroStratum O 4 (M + 4) (X ^ 4) ∩ shallowSet O 4 (M + 4))
        \ pureFaceSet O 4 (M + 4))
      = decidedSet O 4 mixedType4 (M + 4)
        ∩ ((levelZeroStratum O 4 (M + 4) (X ^ 4) ∩ shallowSet O 4 (M + 4))
          \ pureFaceSet O 4 (M + 4)) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hassoc, remainder_carrier_four hK]
  have hsubA : box31a O (M + 4) ⊆ decidedSet O 4 mixedType4 (M + 4) := by
    intro c hc
    rw [mem_box31a_iff] at hc
    exact decidedAt_quartic_31 (t := 1) (by omega) (by norm_num) (by norm_num)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hsubB : box31b O (M + 4) ⊆ decidedSet O 4 mixedType4 (M + 4) := by
    intro c hc
    rw [mem_box31b_iff] at hc
    exact decidedAt_quartic_31 (t := 2) (by omega) (by norm_num) (by norm_num)
      hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hFdis : decidedSet O 4 mixedType4 (M + 4) ∩ forcedBox O (M + 4)
      = (∅ : Set (Coeff O 4 (M + 4))) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hdec, hd3, hd2, hcase⟩
    exact not_decidedAt_of_forced_of_odd (by omega) (stratum_of_forced hd3 hd2 hcase)
      hcase (σ := mixedType4) (by decide) hdec
  rw [Set.inter_union_distrib_left, Set.inter_union_distrib_left, hFdis, Set.union_empty,
    Set.inter_eq_self_of_subset_right hsubA, Set.inter_eq_self_of_subset_right hsubB]
  haveI : Fintype (Coeff O 4 (M + 4)) := Fintype.ofFinite _
  have hdisj : Disjoint (box31a O (M + 4)) (box31b O (M + 4)) := by
    rw [Set.disjoint_left]
    intro c hcA hcB
    rw [mem_box31a_iff] at hcA
    rw [mem_box31b_iff] at hcB
    omega
  rw [Nat.card_coe_set_eq, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_box31a hK, card_box31b hK]

/-- At every OTHER type with all ramification indices odd, the mass-4 remainder
VANISHES (the decided boxes are `mixedType4`-decided; the forced sector always
ramifies evenly). -/
theorem coneRemainderCount_four_ne_of_odd {σ : FactorizationType} (hσ : σ ≠ mixedType4)
    (hodd : ∀ p ∈ σ.data, ¬ 2 ∣ p.1) (M : ℕ) :
    coneRemainderCount O 4 σ M = 0 := by
  classical
  unfold coneRemainderCount
  have hK : 4 ≤ M + 4 := by omega
  have hassoc : ((decidedSet O 4 σ (M + 4)
        ∩ levelZeroStratum O 4 (M + 4) (X ^ 4) ∩ shallowSet O 4 (M + 4))
        \ pureFaceSet O 4 (M + 4))
      = decidedSet O 4 σ (M + 4)
        ∩ ((levelZeroStratum O 4 (M + 4) (X ^ 4) ∩ shallowSet O 4 (M + 4))
          \ pureFaceSet O 4 (M + 4)) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hempty : decidedSet O 4 σ (M + 4)
      ∩ ((box31a O (M + 4) ∪ box31b O (M + 4)) ∪ forcedBox O (M + 4))
      = (∅ : Set (Coeff O 4 (M + 4))) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hdec, (hcA | hcB) | hcF⟩
    · rw [mem_box31a_iff] at hcA
      have hdec2 : DecidedAt O 4 mixedType4 (M + 4) c :=
        decidedAt_quartic_31 (t := 1) (by omega) (by norm_num) (by norm_num)
          hcA.1 hcA.2.1 hcA.2.2.1 hcA.2.2.2
      exact hσ (decidedAt_unique hdec hdec2)
    · rw [mem_box31b_iff] at hcB
      have hdec2 : DecidedAt O 4 mixedType4 (M + 4) c :=
        decidedAt_quartic_31 (t := 2) (by omega) (by norm_num) (by norm_num)
          hcB.1 hcB.2.1 hcB.2.2.1 hcB.2.2.2
      exact hσ (decidedAt_unique hdec hdec2)
    · obtain ⟨hd3, hd2, hcase⟩ := hcF
      exact not_decidedAt_of_forced_of_odd (by omega) (stratum_of_forced hd3 hd2 hcase)
        hcase hodd hdec
  rw [hassoc, remainder_carrier_four hK, hempty]
  rw [Nat.card_coe_set_eq, Set.ncard_empty]

end Count

/-! ## §5 — ★★★ the mass-4 remainder laws at the odd-ramification types -/

section Law

/-- ★★★ **`ConeRemainderLaw 4 ⟨{(1,1),(3,1)}⟩`** — the census family's `e = 4` member at
the mixed type, closed with the constant value `(q−1)/q⁶ + (q−1)/q⁹`. -/
theorem coneRemainderLaw_four_mixed : ConeRemainderLaw 4 mixedType4 := by
  refine ((ZcURLim_qmonomial 6).add (ZcURLim_qmonomial 9)).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (((residueCard O : ℕ) : ℝ) - 1) / ((residueCard O : ℕ) : ℝ) ^ 6
      + (((residueCard O : ℕ) : ℝ) - 1) / ((residueCard O : ℕ) : ℝ) ^ 9
    = (coneRemainderCount O 4 mixedType4 M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  rw [coneRemainderCount_four_mixed M]
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast [Nat.cast_sub (by omega : 1 ≤ residueCard O)]
  rw [add_div]
  congr 1
  · rw [show 4 * (M + 4) = (4 * (M + 4) - 6) + 6 from by omega, pow_add]
    have hA : ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4) - 6) ≠ 0 := pow_ne_zero _ hqR
    have hB : ((residueCard O : ℕ) : ℝ) ^ 6 ≠ 0 := pow_ne_zero _ hqR
    field_simp
    rw [show 4 * (M + 4) - 6 + 6 - 6 = 4 * (M + 4) - 6 from by omega]
  · rw [show 4 * (M + 4) = (4 * (M + 4) - 9) + 9 from by omega, pow_add]
    have hA : ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4) - 9) ≠ 0 := pow_ne_zero _ hqR
    have hB : ((residueCard O : ℕ) : ℝ) ^ 9 ≠ 0 := pow_ne_zero _ hqR
    field_simp
    rw [show 4 * (M + 4) - 9 + 9 - 9 = 4 * (M + 4) - 9 from by omega]

/-- ★★★ **The odd-ramification closure**: `ConeRemainderLaw 4 σ` for EVERY type σ all of
whose ramification indices are odd — the value law at `{(1,1),(3,1)}`, the zero law
everywhere else (in particular at all five unramified degree-4 types). -/
theorem coneRemainderLaw_four_of_odd {σ : FactorizationType}
    (hodd : ∀ p ∈ σ.data, ¬ 2 ∣ p.1) : ConeRemainderLaw 4 σ := by
  by_cases hσ : σ = mixedType4
  · subst hσ
    exact coneRemainderLaw_four_mixed
  · refine ZcURLim_zero.congr ?_
    intro O _ _ _ _ _ π hπ M
    show (0 : ℝ) = (coneRemainderCount O 4 σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
    rw [coneRemainderCount_four_ne_of_odd hσ hodd M]
    simp

/-- ★★ **The `e = 4` reduction**: the whole `m = 4` remainder family follows from the
laws at the types CARRYING AN EVEN ramification index (at degree 4: exactly
`{(1,1),(1,1),(2,1)}`, `{(1,2),(2,1)}`, `{(2,1),(2,1)}`, `{(2,2)}`, `{(4,1)}`). -/
theorem coneRemainderLaw_four_of_evenRam
    (h : ∀ σ : FactorizationType, (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ)
    (σ : FactorizationType) : ConeRemainderLaw 4 σ := by
  by_cases hev : ∃ p ∈ σ.data, 2 ∣ p.1
  · exact h σ hev
  · exact coneRemainderLaw_four_of_odd (fun p hp h2 => hev ⟨p, hp, h2⟩)

/-- The `m = 4` zero-cone clause at every odd-ramification type. -/
theorem zeroConeClause_four_of_odd {σ : FactorizationType}
    (hodd : ∀ p ∈ σ.data, ¬ 2 ∣ p.1) : ZeroConeClause 4 σ :=
  zeroConeClause_of_remainderLaw (by norm_num) σ (coneRemainderLaw_four_of_odd hodd)

end Law

/-! ## §6 — ★★★ the census front, re-based through this file -/

section Front

open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG25 (UnramifiedBlockBridge)
open Uniformity.Density.IFCG26 (decidedSliceAt_all_of_remainder4_bridge)

/-- ★★★ **THE CENSUS FRONT, re-based through this file**: with the odd-ramification
`e = 4` members closed here, the all-degree decided slice rests on EXACTLY the remainder
laws at `e ≥ 5`, the `e = 4` laws at the even-ramification types, and the unramified
block bridges. -/
theorem decidedSliceAt_all_of_remainder5_even4_bridge
    (hR : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ → ConeRemainderLaw e σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ)
    (hBr : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n := by
  refine decidedSliceAt_all_of_remainder4_bridge ?_ hBr
  intro e he hsm σ hσ hwit
  rcases Nat.lt_or_ge e 5 with h5 | h5
  · have he4 : e = 4 := by omega
    subst he4
    by_cases hev : ∃ p ∈ σ.data, 2 ∣ p.1
    · exact hR4 σ hσ hwit hev
    · exact coneRemainderLaw_four_of_odd (fun p hp h2 => hev ⟨p, hp, h2⟩)
  · exact hR e h5 hsm σ hσ hwit

end Front

end Uniformity.Density.IFCG31

end

/-! ## AXCHECK FOOTER — §1 expects Lean core `{propext, Classical.choice, Quot.sound}`;
§§2–6 expect Lean core PLUS exactly the signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42).  The C.33 cites must NOT
occur. -/

#print axioms Uniformity.Density.IFCG31.remainder_carrier_four
#print axioms Uniformity.Density.IFCG31.card_box31a
#print axioms Uniformity.Density.IFCG31.card_box31b
#print axioms Uniformity.Density.IFCG31.decidedAt_quartic_31
#print axioms Uniformity.Density.IFCG31.forces_even_ram_of_forced
#print axioms Uniformity.Density.IFCG31.decidedAt_forced_split
#print axioms Uniformity.Density.IFCG31.not_decidedAt_of_forced_of_odd
#print axioms Uniformity.Density.IFCG31.coneRemainderCount_four_mixed
#print axioms Uniformity.Density.IFCG31.coneRemainderCount_four_ne_of_odd
#print axioms Uniformity.Density.IFCG31.coneRemainderLaw_four_mixed
#print axioms Uniformity.Density.IFCG31.coneRemainderLaw_four_of_odd
#print axioms Uniformity.Density.IFCG31.coneRemainderLaw_four_of_evenRam
#print axioms Uniformity.Density.IFCG31.zeroConeClause_four_of_odd
#print axioms Uniformity.Density.IFCG31.decidedSliceAt_all_of_remainder5_even4_bridge
