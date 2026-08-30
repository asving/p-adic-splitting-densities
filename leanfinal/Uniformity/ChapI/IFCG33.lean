/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG26
import Uniformity.ChapI.IFCG31

/-!
# Uniformity.ChapI.IFCG33 — [UZL 2026-08-30] the unramified zero-law at EVERY mass:
the wide-face generalization

Stage UZL of the cone census (design record `runs/wave-c/verdict_UZL.md`).  CCA
(`IFCG31`) closed the `m = 4` remainder family at every odd-ramification type and
RECORDED THE CONJECTURE: the all-unramified zero laws should close at EVERY mass via a
wide-face generalization of WFR's `staircase_not_shallow`.  This file proves it —
uniformly in `q`, `m`, `σ` — by a mechanism SHARPER than the conjectured route:

* **§1 ★★ the wide-face lemma** (`exists_visible_fracFace_of_shallow`, Lean-core): every
  SHALLOW stratum class carries a VISIBLE fractional class NP face.  No staircase
  induction and no hull recursion: take `j < m` minimizing `v_j/(m−j)` — the LAST hull
  edge, ending at the monic point `(m, 0)`.  Shallowness (`∃ i₀, v_{i₀} < m−i₀`) makes
  the minimum `< 1`, so its lowest-terms slope `h/e'` has `1 ≤ h < e'` (fractional,
  `e' ≥ 2`); its support is `h·m < e'·K`, so visibility is AUTOMATIC — the deciding face
  never touches the precision ceiling, invisible corner included.
* **§2 ★ the forcing corollaries**: `forces_ram_of_shallow` — every lift of a shallow
  stratum class has a monic irreducible factor of ramification index divisible by some
  `e' ≥ 2` (CRL's `fracFaceForcesRam_of_stratum`, already uniform in `m`); hence
  `not_decidedAt_unramified_of_shallow` — NO unramified type is EVER decided on the
  shallow stratum (pure faces need not even be excluded).  Plus the uniform-`m` odd-half
  tool `not_decidedAt_of_evenFace_of_odd` (the even-ram successor's exclusion engine:
  IFCG31 §3's shape at every mass).
* **§3 the zero count**: `coneRemainderCount m σ M = 0` at EVERY level, every `m`, every
  unramified σ.
* **§4 ★★★ THE LAWS**: `ConeRemainderLaw m σ` (value 0) and `ZeroConeClause m σ` for
  every `m` and every unramified σ — the conjectured family, closed at once.
* **§5 ★★★ the census front re-based** (`decidedSliceAt_all_of_ram5_even4_bridge`): the
  all-degree decided slice now rests on EXACTLY the remainder laws at `e ≥ 5` for
  genuinely RAMIFIED types (`∃ p ∈ σ.data, p.1 ≠ 1`), the `e = 4` laws at the five
  even-ramification types, and the block bridges.

## The honest fence

The all-odd-`e` zero law does NOT generalize: IFCG31's `coneRemainderCount_four_mixed`
is NONZERO at the all-odd type `{(1,1),(3,1)}` — the `m = 4` all-odd closure was
value-law-dependent (it needed the decided sector's exact count).  The uniform content
is (a) the unramified ZERO law (this file) and (b) the even-face exclusion tool (§2);
the odd-ram VALUE laws at each mass stay with the census recursion.

## Axiom fence

§1 is Lean core `{propext, Classical.choice, Quot.sound}`.  §§2–4 consume exactly ONE
extra axiom, inherited through IFCG26's forcing: the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42).  §5 inherits IFCG31's front
footprint (B.42 only).  Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG33

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply classNPSupport_le le_classNPSupport)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero shallowSet mem_stratum_X_pow_iff
  pureFaceSet coneRemainderCount ConeRemainderLaw ZeroConeClause
  zeroConeClause_of_remainderLaw npHeight_coe)
open Uniformity.Density.IFCG26 (fracFaceForcesRam_of_stratum)

attribute [local instance] Classical.propDecidable

/-! ## §1 — ★★ the wide-face lemma: shallow stratum classes have a visible
fractional face -/

section WideFace

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- ★★ **The wide-face lemma** (the staircase conjecture, closed by the LAST hull edge):
every shallow stratum class polygon has a visible fractional face.  Choose `j < m`
minimizing `v_j/(m−j)`; shallowness makes the minimum `< 1`, so the lowest-terms slope
`h/e'` satisfies `1 ≤ h < e'` (so `e' ≥ 2`), the support is `h·m` attained at `j` and
the monic point `m`, and `h·m < e'·K` gives visibility outright. -/
theorem exists_visible_fracFace_of_shallow {m K : ℕ} (hmK : m ≤ K) {c : Coeff O m K}
    (hstr : ∀ i : Fin m, 1 ≤ resOrd (c i)) (hsh : c ∈ shallowSet O m K) :
    ∃ h e' : ℕ, 1 ≤ h ∧ h < e' ∧ Nat.Coprime h e'
      ∧ ClassNPFace c h e' ∧ NPVisibleAt c h e' := by
  obtain ⟨i₀, hi₀⟩ := hsh
  -- STEP 1: the argmin abscissa of the last-edge slope `v_i/(m−i)` over `i < m`
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin m => (resOrd (c i) : ℚ) / ((m - (i : ℕ) : ℕ) : ℚ))
    ⟨i₀, Finset.mem_univ i₀⟩
  have hmin : ∀ i : Fin m,
      resOrd (c j) * (m - (i : ℕ)) ≤ resOrd (c i) * (m - (j : ℕ)) := by
    intro i
    have h1 := hj i (Finset.mem_univ i)
    have hdi : (0 : ℚ) < ((m - (i : ℕ) : ℕ) : ℚ) := by
      have h5 := i.isLt
      exact_mod_cast (by omega : 0 < m - (i : ℕ))
    have hdj : (0 : ℚ) < ((m - (j : ℕ) : ℕ) : ℚ) := by
      have h5 := j.isLt
      exact_mod_cast (by omega : 0 < m - (j : ℕ))
    rw [div_le_div_iff₀ hdj hdi] at h1
    exact_mod_cast h1
  -- STEP 2: shallowness makes the min slope `< 1`: `1 ≤ v_j < m − j`
  have hjlt := j.isLt
  have hvj1 : 1 ≤ resOrd (c j) := hstr j
  have hvjw : resOrd (c j) < m - (j : ℕ) := by
    have h1 := hmin i₀
    have h2 : resOrd (c i₀) * (m - (j : ℕ)) < (m - (i₀ : ℕ)) * (m - (j : ℕ)) :=
      mul_lt_mul_of_pos_right hi₀ (by omega : 0 < m - (j : ℕ))
    have h3 : resOrd (c j) * (m - (i₀ : ℕ)) < (m - (i₀ : ℕ)) * (m - (j : ℕ)) :=
      lt_of_le_of_lt h1 h2
    rw [Nat.mul_comm (resOrd (c j)) (m - (i₀ : ℕ))] at h3
    exact Nat.lt_of_mul_lt_mul_left h3
  -- STEP 3: lowest terms `h/e' = v_j/(m−j)`
  set g := Nat.gcd (resOrd (c j)) (m - (j : ℕ)) with hg
  have hdpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega : 0 < resOrd (c j))
  obtain ⟨h, hh⟩ := Nat.gcd_dvd_left (resOrd (c j)) (m - (j : ℕ))
  obtain ⟨e', he'⟩ := Nat.gcd_dvd_right (resOrd (c j)) (m - (j : ℕ))
  rw [← hg] at hh he'
  have hcop : Nat.Coprime h e' := by
    have h5 : g * Nat.gcd h e' = g * 1 := by
      rw [Nat.mul_one]
      calc g * Nat.gcd h e' = Nat.gcd (g * h) (g * e') := (Nat.gcd_mul_left g h e').symm
        _ = Nat.gcd (resOrd (c j)) (m - (j : ℕ)) := by rw [← hh, ← he']
        _ = g := hg.symm
    exact Nat.eq_of_mul_eq_mul_left hdpos h5
  have hh1 : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with rfl | h5
    · rw [Nat.mul_zero] at hh
      omega
    · exact h5
  have hhe : h < e' := by
    have h5 : g * h < g * e' := by
      rw [← hh, ← he']
      exact hvjw
    exact Nat.lt_of_mul_lt_mul_left h5
  -- STEP 4: the support is `h·m`, attained at `j` and at the monic point `m`
  have hnpm : npHeight c m = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl m)]
  have hkey : ∀ i : Fin m, h * (m - (i : ℕ)) ≤ e' * resOrd (c i) := by
    intro i
    have h6 := hmin i
    have h7 : g * (h * (m - (i : ℕ))) ≤ g * (e' * resOrd (c i)) := by
      calc g * (h * (m - (i : ℕ))) = (g * h) * (m - (i : ℕ)) := by ring
        _ = resOrd (c j) * (m - (i : ℕ)) := by rw [← hh]
        _ ≤ resOrd (c i) * (m - (j : ℕ)) := h6
        _ = resOrd (c i) * (g * e') := by rw [← he']
        _ = g * (e' * resOrd (c i)) := by ring
    exact Nat.le_of_mul_le_mul_left h7 hdpos
  have hsup : classNPSupport c h e' = h * m := by
    refine le_antisymm (classNPSupport_le c h e') (le_classNPSupport ?_)
    intro i him
    rcases Nat.lt_or_ge i m with hlt | hge
    · have hnp : npHeight c i = resOrd (c ⟨i, hlt⟩) := by
        have h5 := npHeight_coe c ⟨i, hlt⟩
        simpa using h5
      rw [hnp]
      have h8 := hkey ⟨i, hlt⟩
      calc h * m = h * (m - i) + h * i := by
            rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hlt)]
        _ ≤ e' * resOrd (c ⟨i, hlt⟩) + h * i := Nat.add_le_add_right h8 _
    · have him' : i = m := le_antisymm him hge
      subst him'
      rw [hnpm, Nat.mul_zero, Nat.zero_add]
  have hAj : NPAttains c h e' (j : ℕ) := by
    refine ⟨le_of_lt hjlt, ?_⟩
    rw [hsup, npHeight_coe c j]
    have h5 : e' * resOrd (c j) = h * (m - (j : ℕ)) := by
      calc e' * resOrd (c j) = e' * (g * h) := by rw [← hh]
        _ = h * (g * e') := by ring
        _ = h * (m - (j : ℕ)) := by rw [← he']
    rw [h5, ← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hjlt)]
  have hAm : NPAttains c h e' m := by
    refine ⟨le_refl m, ?_⟩
    rw [hsup, hnpm, Nat.mul_zero, Nat.zero_add]
  -- STEP 5: visibility is automatic — `h·m < e'·m ≤ e'·K`
  have hvisi : NPVisibleAt c h e' := by
    show classNPSupport c h e' < e' * K
    rw [hsup]
    calc h * m < e' * m := mul_lt_mul_of_pos_right hhe (by omega : 0 < m)
      _ ≤ e' * K := Nat.mul_le_mul (le_refl e') hmK
  exact ⟨h, e', hh1, hhe, hcop, ⟨(j : ℕ), m, hjlt, hAj, hAm⟩, hvisi⟩

end WideFace

/-! ## §2 — ★ the forcing corollaries -/

section Forcing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **The shallow-stratum ramification forcing**: every lift of a shallow stratum
class has a monic irreducible factor whose ramification index is divisible by some
`e' ≥ 2`. -/
theorem forces_ram_of_shallow {m K : ℕ} (hmK : m ≤ K) {c : Coeff O m K}
    (hstr : c ∈ levelZeroStratum O m K (X ^ m)) (hsh : c ∈ shallowSet O m K)
    {a : Fin m → O} (ha : proj O m K a = c) :
    ∃ g' ∈ monicFactors (monicPoly a), ∃ e' : ℕ, 2 ≤ e' ∧ e' ∣ ramIndexOf g' := by
  obtain ⟨i₀, hi₀⟩ := hsh
  have hK1 : 1 ≤ K := by
    have := i₀.isLt
    omega
  have hstr' : ∀ i : Fin m, 1 ≤ resOrd (c i) := (mem_stratum_X_pow_iff hK1 c).1 hstr
  obtain ⟨h, e', hh1, hhe, hcop, hface, hvis⟩ :=
    exists_visible_fracFace_of_shallow hmK hstr' ⟨i₀, hi₀⟩
  obtain ⟨g', hg', hdvd⟩ :=
    fracFaceForcesRam_of_stratum (by omega : 2 ≤ e') hcop hstr hface hvis ha
  exact ⟨g', hg', e', by omega, hdvd⟩

/-- ★ **The unramified zero-decision**: NO type all of whose ramification indices are
`1` is ever decided on the shallow stratum — at every mass, every level `K ≥ m`. -/
theorem not_decidedAt_unramified_of_shallow {m K : ℕ} (hmK : m ≤ K) {c : Coeff O m K}
    (hstr : c ∈ levelZeroStratum O m K (X ^ m)) (hsh : c ∈ shallowSet O m K)
    {σ : FactorizationType} (hunr : ∀ p ∈ σ.data, p.1 = 1) :
    ¬ DecidedAt O m σ K c := by
  intro hdec
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  obtain ⟨g', hg', e', he'2, hdvd⟩ := forces_ram_of_shallow hmK hstr hsh ha
  have hmem : efPair g' ∈ (typeOf (monicPoly a)).data := by
    rw [typeOf_data]
    exact Multiset.mem_map_of_mem _ hg'
  rw [hdec a ha] at hmem
  have h1 : (efPair g').1 = 1 := hunr _ hmem
  have h2 : e' ∣ (efPair g').1 := hdvd
  rw [h1] at h2
  have h3 := Nat.le_of_dvd Nat.one_pos h2
  omega

/-- The uniform-`m` odd-half exclusion tool (IFCG31 §3's shape at every mass, for the
even-ramification successor): a visible class face with EVEN denominator excludes every
all-odd-ramification type. -/
theorem not_decidedAt_of_evenFace_of_odd {m K h e' : ℕ} (he' : 2 ≤ e') (heven : 2 ∣ e')
    (hcop : Nat.Coprime h e') {c : Coeff O m K}
    (hstr : c ∈ levelZeroStratum O m K (X ^ m))
    (hface : ClassNPFace c h e') (hvis : NPVisibleAt c h e')
    {σ : FactorizationType} (hodd : ∀ p ∈ σ.data, ¬ 2 ∣ p.1) :
    ¬ DecidedAt O m σ K c := by
  intro hdec
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  obtain ⟨g', hg', hdvd⟩ := fracFaceForcesRam_of_stratum he' hcop hstr hface hvis ha
  have h2dvd : 2 ∣ ramIndexOf g' := dvd_trans heven hdvd
  have hmem : efPair g' ∈ (typeOf (monicPoly a)).data := by
    rw [typeOf_data]
    exact Multiset.mem_map_of_mem _ hg'
  rw [hdec a ha] at hmem
  exact hodd _ hmem h2dvd

end Forcing

/-! ## §3 — the zero count at every level -/

section Count

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- **The unramified remainder count is IDENTICALLY ZERO** — every mass, every level,
every complete DVR. -/
theorem coneRemainderCount_unramified (m : ℕ) {σ : FactorizationType}
    (hunr : ∀ p ∈ σ.data, p.1 = 1) (M : ℕ) :
    coneRemainderCount O m σ M = 0 := by
  classical
  unfold coneRemainderCount
  have hempty : ((decidedSet O m σ (M + m)
        ∩ levelZeroStratum O m (M + m) (X ^ m)
        ∩ shallowSet O m (M + m))
      \ pureFaceSet O m (M + m)) = (∅ : Set (Coeff O m (M + m))) := by
    ext c
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨⟨hdec, hstr⟩, hsh⟩, -⟩
    exact not_decidedAt_unramified_of_shallow (by omega : m ≤ M + m) hstr hsh hunr hdec
  rw [hempty, Nat.card_coe_set_eq, Set.ncard_empty]

end Count

/-! ## §4 — ★★★ THE LAWS: the conjectured family, closed at once -/

section Law

/-- ★★★ **THE UNRAMIFIED ZERO-LAW AT EVERY MASS**: `ConeRemainderLaw m σ` holds with
value `0` for EVERY `m` and EVERY type σ all of whose ramification indices are `1` —
uniform in `q`, every complete DVR, every uniformizer.  CCA's recorded conjecture,
proved. -/
theorem coneRemainderLaw_unramified (m : ℕ) {σ : FactorizationType}
    (hunr : ∀ p ∈ σ.data, p.1 = 1) : ConeRemainderLaw m σ := by
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  show (0 : ℝ) = (coneRemainderCount O m σ M : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [coneRemainderCount_unramified m hunr M]
  simp

/-- ★★ The zero-cone clause at every mass and every unramified type. -/
theorem zeroConeClause_unramified {m : ℕ} (hm : 0 < m) {σ : FactorizationType}
    (hunr : ∀ p ∈ σ.data, p.1 = 1) : ZeroConeClause m σ :=
  zeroConeClause_of_remainderLaw hm σ (coneRemainderLaw_unramified m hunr)

end Law

/-! ## §5 — ★★★ the census front, re-based through this file -/

section Front

open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG25 (UnramifiedBlockBridge)
open Uniformity.Density.IFCG31 (decidedSliceAt_all_of_remainder5_even4_bridge)

/-- ★★★ **THE CENSUS FRONT, re-based through this file**: with the unramified zero-laws
closed at EVERY mass, the all-degree decided slice rests on EXACTLY the remainder laws
at `e ≥ 5` for the genuinely RAMIFIED types (`∃ p ∈ σ.data, p.1 ≠ 1`), the `e = 4` laws
at the five even-ramification types, and the unramified block bridges. -/
theorem decidedSliceAt_all_of_ram5_even4_bridge
    (hR : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ConeRemainderLaw e σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ)
    (hBr : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n := by
  refine decidedSliceAt_all_of_remainder5_even4_bridge ?_ hR4 hBr
  intro e he hsm σ hσ hwit
  by_cases hram : ∃ p ∈ σ.data, p.1 ≠ 1
  · exact hR e he hsm σ hσ hwit hram
  · refine coneRemainderLaw_unramified e fun p hp => ?_
    by_contra h1
    exact hram ⟨p, hp, h1⟩

end Front

end Uniformity.Density.IFCG33

end

/-! ## AXCHECK FOOTER — §1 expects Lean core `{propext, Classical.choice, Quot.sound}`;
§§2–5 expect Lean core PLUS exactly the signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42).  The C.33 cites must NOT
occur. -/

#print axioms Uniformity.Density.IFCG33.exists_visible_fracFace_of_shallow
#print axioms Uniformity.Density.IFCG33.forces_ram_of_shallow
#print axioms Uniformity.Density.IFCG33.not_decidedAt_unramified_of_shallow
#print axioms Uniformity.Density.IFCG33.not_decidedAt_of_evenFace_of_odd
#print axioms Uniformity.Density.IFCG33.coneRemainderCount_unramified
#print axioms Uniformity.Density.IFCG33.coneRemainderLaw_unramified
#print axioms Uniformity.Density.IFCG33.zeroConeClause_unramified
#print axioms Uniformity.Density.IFCG33.decidedSliceAt_all_of_ram5_even4_bridge
