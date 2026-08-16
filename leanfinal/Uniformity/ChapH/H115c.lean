/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapH.H115b
import Uniformity.ChapH.H13

/-!
# Uniformity.ChapH.H115c — every α ghost fibre is `Q ^ (k · c(m))` (H.115 clause iii)

**Chapter H, NODE H.115, SPLIT c** (`blueprint/CHAP-H_general_induction.md` §17.2, the
blueprint's mandated split H.115a/H.115b/H.115c).

`card_alphaFiber` — at a realized slope `k` and a nonzero residue `z`, the set of α(k, z) states
with a PRESCRIBED α child `d` has exactly `Q ^ (k · clusterC m)` elements,
`clusterC m = m (m − 1) / 2`.

## The parametrization, in one paragraph

H.115b's inverse shear says the fibre is the image of the child's lifts: `c` is an α(k, z) state
with child `d` exactly when `c` is carried by `alphaParentCoeff π b k ŵ` for some lift `b` of `d`
with coordinates in `𝔪` (`mem_alphaFiber_iff`), where `ŵ = resSect O z` is the pinned centre and
`alphaParentCoeff π b k ŵ j = (alphaFrame b ŵ).coeff j · (π ^ k) ^ (m − j)`.  So the count is the
number of lifts `b` of `d` MODULO the kernel of `b ↦ proj O m N (alphaParentCoeff π b k ŵ)`, and
`proj_alphaParentCoeff_eq_iff` computes that kernel EXACTLY: `b` and `b'` give the same parent
class iff `π ^ (N − m k + k j)` divides `b j − b' j` for every `j`.  Two lifts of `d` already
agree mod `π ^ (N − m k)`, so coordinate `j` carries exactly `k · j` free digits and the fibre
has `∏_{j < m} Q ^ (k j) = Q ^ (k · m (m − 1) / 2)` elements — the R2 unit-pivot count, and the
battery's measured fibre size.

## Where the unit pivots are

The graded kernel is where H.60's triangularity enters this file, in the sharp form it is needed:
`pow_dvd_coeff_comp_X_add_C` says composition with `X + C v` moves coefficient `j` using only
coefficients `i ≥ j`, so a MONOTONE divisibility profile passes through it — in BOTH directions,
because `X + C v` is invertible as a substitution (`X + C (−v)` undoes it).  That two-sided
triangularity is exactly "triangular with unit pivots"; no back-substitution recursion is needed,
the inverse substitution does the back-substitution.

DEPENDS: H.115a (`resSect`, `alphaChild`, `alphaChild_spec`, `divPow`), H.115b (`alphaFrame`,
`alphaParent`, `alphaParent_recentre`, `exists_isAlphaState_of_alphaParent`,
`coeff_eq_of_monicPoly_eq_alphaParent`, `mem_maximalIdeal_of_monicPoly_eq_alphaParent`), H.111
(`IsAlphaState`), H.107 (`mem_maximalIdeal_pow_iff_dvd_of_irr`), H.13 (`clusterC`), H.100
(`classSect` via H.115a) · landed `Res`, `card_res`, `proj`, `monicPoly`
(`Uniformity/Density/LocalData.lean`, `Uniformity/Density/Transport.lean`) · mathlib
`Nat.card_eq_of_bijective`, `Nat.card_pi`, `Finset.prod_pow_eq_pow_sum`, `Finset.sum_range_id`,
`Nat.choose_two_right`, `Polynomial.leadingCoeff_comp`.

**ENVIRONMENT — ENV-H17** + `π` explicit + `[Finite (ResidueField O)]` (clause (iii) counts).

## TEETH (GC-8)

Battery `P1(d) alpha fibres exact+onto, all (k,z) slices` of
`verification/openmath/OM2_genindb_battery.py` — the exhaustive fibre histogram, every fibre
EXACTLY `Q ^ (k · c(m))`.  The teeth cover the PINNED map only (LESSON L-BATT).  The `#guard`s
at the end reproduce the fibre exponent as the product-of-coordinates count
`∏_{j < m} Q ^ (k j)` at every realized slope of the battery's `part1` plan.

## Status

Sorry-free, axiom-free (Lean core only); footprint printed at the end of the file.
-/

namespace Uniformity.Density.Induction

open IsLocalRing Polynomial

/-! ## 1. Composition with `X + C v` is triangular -/

/-- **Triangularity of the substitution `X ↦ X + v`.**  Coefficient `j` of `Q (X + v)` is an
`O`-combination of the coefficients `i ≥ j` of `Q`, so any MONOTONE divisibility profile of `Q`'s
coefficients passes to `Q (X + v)`'s.  Applied twice (at `v` and at `−v`) this is the two-sided
"triangular with unit pivots" statement the fibre count needs. -/
theorem pow_dvd_coeff_comp_X_add_C {O : Type*} [CommRing O] {π : O} {n : ℕ → ℕ}
    (hn : Monotone n) {Q : Polynomial O} (hQ : ∀ i, π ^ n i ∣ Q.coeff i) (v : O) (j : ℕ) :
    π ^ n j ∣ (Q.comp (X + C v)).coeff j := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, finsetSum_coeff]
  refine Finset.dvd_sum fun i _ => ?_
  rw [coeff_C_mul]
  rcases Nat.lt_or_ge i j with hij | hij
  · have hlin : (X + C v : Polynomial O).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
    have hd : ((X + C v : Polynomial O) ^ i).natDegree < j :=
      lt_of_le_of_lt (natDegree_pow_le.trans (by
        calc i * (X + C v : Polynomial O).natDegree ≤ i * 1 := Nat.mul_le_mul_left i hlin
          _ = i := by omega)) hij
    rw [coeff_eq_zero_of_natDegree_lt hd, mul_zero]
    exact dvd_zero _
  · exact Dvd.dvd.mul_right ((pow_dvd_pow π (hn hij)).trans (hQ i)) _

/-- **The recentring substitution is injective on polynomials.**  `p ↦ p (t (X + w))` with
`t ≠ 0` over a domain: the leading coefficient of the composite is `p.leadingCoeff · t ^ deg p`,
nonzero whenever `p` is. -/
theorem comp_recentre_injective {O : Type*} [CommRing O] [IsDomain O] {t : O} (ht : t ≠ 0)
    (w : O) {p q : Polynomial O} (h : p.comp (C t * (X + C w)) = q.comp (C t * (X + C w))) :
    p = q := by
  by_contra hne
  have hr : p - q ≠ 0 := sub_ne_zero.2 hne
  have hXw : (X + C w : Polynomial O) ≠ 0 := (monic_X_add_C w).ne_zero
  have hCt : (C t : Polynomial O) ≠ 0 := by simpa [Polynomial.C_eq_zero] using ht
  have hdeg : (C t * (X + C w) : Polynomial O).natDegree = 1 := by
    rw [natDegree_mul hCt hXw, natDegree_C, natDegree_X_add_C]
  have hlc : (C t * (X + C w) : Polynomial O).leadingCoeff = t := by
    rw [leadingCoeff_mul, leadingCoeff_C, (monic_X_add_C w).leadingCoeff, mul_one]
  have hzero : (p - q).comp (C t * (X + C w)) = 0 := by
    rw [sub_comp, h, sub_self]
  have hlead := Polynomial.leadingCoeff_comp (p := p - q) (q := C t * (X + C w))
    (by rw [hdeg]; exact one_ne_zero)
  rw [hzero, leadingCoeff_zero, hlc] at hlead
  exact (mul_ne_zero (leadingCoeff_ne_zero.2 hr) (pow_ne_zero _ ht)) hlead.symm

/-! ## 2. The parent's coefficient vector, as a function of the child lift -/

section Fibre

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Level-`N` classes of two coefficient vectors coincide iff the vectors are congruent
coordinatewise mod `π ^ N`. -/
theorem proj_eq_iff_pow_dvd {π : O} (hπ : Irreducible π) {m N : ℕ} (v v' : Fin m → O) :
    proj O m N v = proj O m N v' ↔ ∀ j : Fin m, π ^ N ∣ (v j - v' j) := by
  constructor
  · intro h j
    exact (mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).1 (Ideal.Quotient.eq.1 (congrFun h j))
  · intro h
    funext j
    exact Ideal.Quotient.eq.2 ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).2 (h j))

/-- **The parent's coefficient vector**, as an explicit function of the child lift: the inverse
shear `alphaParent π b k ŵ` read coordinatewise (H.115b's `alphaParent_coeff`). -/
noncomputable def alphaParentCoeff (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) :
    Fin m → O :=
  fun j => (alphaFrame b ŵ).coeff (j : ℕ) * (π ^ k) ^ (m - (j : ℕ))

theorem monicPoly_alphaParentCoeff (π : O) {m : ℕ} (b : Fin m → O) (k : ℕ) (ŵ : O) :
    monicPoly (alphaParentCoeff π b k ŵ) = alphaParent π b k ŵ := by
  refine Polynomial.ext fun j => ?_
  rw [alphaParent_coeff]
  rcases lt_trichotomy j m with hj | hj | hj
  · rw [monicPoly_coeff_lt _ hj]
    rfl
  · have h1 : (monicPoly (alphaParentCoeff π b k ŵ)).coeff j = 1 := by
      have h := (monicPoly_monic (alphaParentCoeff π b k ŵ)).coeff_natDegree
      rw [monicPoly_natDegree] at h
      rw [hj]; exact h
    have h2 : (alphaFrame b ŵ).coeff j = 1 := by
      have h := (alphaFrame_monic b ŵ).coeff_natDegree
      rw [alphaFrame_natDegree] at h
      rw [hj]; exact h
    rw [h1, h2, hj, Nat.sub_self, pow_zero, one_mul]
  · have h1 : (monicPoly (alphaParentCoeff π b k ŵ)).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega)
    have h2 : (alphaFrame b ŵ).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [alphaFrame_natDegree]; omega)
    rw [h1, h2, zero_mul]

/-! ## 3. The kernel of the shear, exactly -/

/-- **The graded kernel of the α shear.**  Two child lifts have the same level-`N` parent class
iff they agree coordinatewise at the GRADED windows `N − m k + k j`: coordinate `j` of the parent
carries the factor `π ^ (k (m − j))`, and the substitution `X ↦ X − ŵ` is triangular in both
directions, so the graded profile transfers unchanged. -/
theorem proj_alphaParentCoeff_eq_iff {π : O} (hπ : Irreducible π) {m N k : ℕ} (hm : 1 ≤ m)
    (hmk : m * k ≤ N) (ŵ : O) (b b' : Fin m → O) :
    proj O m N (alphaParentCoeff π b k ŵ) = proj O m N (alphaParentCoeff π b' k ŵ) ↔
      ∀ j : Fin m, π ^ (N - m * k + k * (j : ℕ)) ∣ (b j - b' j) := by
  classical
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hnmono : Monotone (fun i => N - m * k + k * i) := by
    intro i i' hii
    exact Nat.add_le_add_left (Nat.mul_le_mul_left k hii) _
  -- the two difference polynomials, and the substitutions relating them
  have hQlt : ∀ (i : ℕ) (h : i < m),
      (monicPoly b - monicPoly b').coeff i = b ⟨i, h⟩ - b' ⟨i, h⟩ := by
    intro i h
    rw [coeff_sub, monicPoly_coeff_lt b h, monicPoly_coeff_lt b' h]
  have hQge : ∀ i : ℕ, m ≤ i → (monicPoly b - monicPoly b').coeff i = 0 := by
    intro i hi
    rw [coeff_sub]
    rcases eq_or_lt_of_le hi with he | hlt
    · have h1 := (monicPoly_monic b).coeff_natDegree
      have h2 := (monicPoly_monic b').coeff_natDegree
      rw [monicPoly_natDegree] at h1
      rw [monicPoly_natDegree] at h2
      rw [← he, h1, h2, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [monicPoly_natDegree]; omega), sub_self]
  have hPQ : alphaFrame b ŵ - alphaFrame b' ŵ
      = (monicPoly b - monicPoly b').comp (X + C (-ŵ)) := by
    rw [sub_comp, alphaFrame, alphaFrame, map_neg, ← sub_eq_add_neg]
  have hQP : monicPoly b - monicPoly b'
      = (alphaFrame b ŵ - alphaFrame b' ŵ).comp (X + C ŵ) := by
    rw [hPQ, Polynomial.comp_assoc]
    have hid : (X + C (-ŵ)).comp (X + C ŵ) = (X : Polynomial O) := by
      rw [add_comp, X_comp, C_comp, map_neg]
      ring
    rw [hid, comp_X]
  have hPge : ∀ j : ℕ, m ≤ j → (alphaFrame b ŵ - alphaFrame b' ŵ).coeff j = 0 := by
    intro j hj
    have hQdeg : (monicPoly b - monicPoly b').natDegree ≤ m - 1 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun i hi => hQge i (by omega)
    have hlin : (X + C (-ŵ) : Polynomial O).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
    refine coeff_eq_zero_of_natDegree_lt ?_
    rw [hPQ]
    refine lt_of_le_of_lt (natDegree_comp_le.trans ?_) (by omega : m - 1 < j)
    calc (monicPoly b - monicPoly b').natDegree * (X + C (-ŵ) : Polynomial O).natDegree
        ≤ (m - 1) * 1 := Nat.mul_le_mul hQdeg hlin
      _ = m - 1 := by omega
  -- coordinate `j` of the parent difference is the frame difference times `π ^ (k (m − j))`
  have hcoeffdiff : ∀ j : Fin m,
      alphaParentCoeff π b k ŵ j - alphaParentCoeff π b' k ŵ j
        = (alphaFrame b ŵ - alphaFrame b' ŵ).coeff (j : ℕ) * π ^ (k * (m - (j : ℕ))) := by
    intro j
    simp only [alphaParentCoeff, coeff_sub, ← pow_mul, sub_mul]
  -- the exponent bookkeeping: `N = (N − m k + k j) + k (m − j)` inside the window
  have hsplit : ∀ j : Fin m, N = (N - m * k + k * (j : ℕ)) + k * (m - (j : ℕ)) := by
    intro j
    have hj : (j : ℕ) < m := j.isLt
    have hsum : k * (m - (j : ℕ)) + k * (j : ℕ) = k * m := by
      rw [← Nat.mul_add]
      congr 1
      omega
    have hkm : m * k = k * m := Nat.mul_comm _ _
    omega
  have hcancel : ∀ j : Fin m,
      (π ^ N ∣ (alphaFrame b ŵ - alphaFrame b' ŵ).coeff (j : ℕ) * π ^ (k * (m - (j : ℕ))))
        ↔ π ^ (N - m * k + k * (j : ℕ)) ∣ (alphaFrame b ŵ - alphaFrame b' ŵ).coeff (j : ℕ) := by
    intro j
    constructor
    · intro h
      rw [hsplit j, pow_add] at h
      exact (mul_dvd_mul_iff_right (pow_ne_zero (k * (m - (j : ℕ))) hπ0)).1 h
    · intro h
      rw [hsplit j, pow_add]
      exact mul_dvd_mul_right h _
  rw [proj_eq_iff_pow_dvd hπ]
  constructor
  · intro h j
    have hP : ∀ i : ℕ, π ^ (N - m * k + k * i) ∣ (alphaFrame b ŵ - alphaFrame b' ŵ).coeff i := by
      intro i
      by_cases hi : i < m
      · have := (hcancel ⟨i, hi⟩).1 (by
          have hh := h ⟨i, hi⟩
          rwa [hcoeffdiff ⟨i, hi⟩] at hh)
        exact this
      · rw [hPge i (by omega)]
        exact dvd_zero _
    have hQd := pow_dvd_coeff_comp_X_add_C (n := fun i => N - m * k + k * i) hnmono hP ŵ (j : ℕ)
    rw [← hQP, hQlt (j : ℕ) j.isLt] at hQd
    simpa using hQd
  · intro h j
    have hQd : ∀ i : ℕ, π ^ (N - m * k + k * i) ∣ (monicPoly b - monicPoly b').coeff i := by
      intro i
      by_cases hi : i < m
      · rw [hQlt i hi]
        simpa using h ⟨i, hi⟩
      · rw [hQge i (by omega)]
        exact dvd_zero _
    have hPd := pow_dvd_coeff_comp_X_add_C (n := fun i => N - m * k + k * i) hnmono hQd (-ŵ)
      (j : ℕ)
    rw [← hPQ] at hPd
    rw [hcoeffdiff j]
    exact (hcancel j).2 hPd

/-! ## 4. The fibre, parametrized by the child's lifts -/

/-- **The α fibre, parametrized.**  A state lies over the child `d` exactly when it is carried by
the inverse shear of some lift of `d` with coordinates in `𝔪`.  Forward is clause (i) plus the
injectivity of the recentring substitution; backward is H.115b's packaged inverse shear. -/
theorem mem_alphaFiber_iff {π : O} (hπ : Irreducible π) {m N k : ℕ} {z : ResidueField O}
    (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1) (hz : z ≠ 0)
    (d : ClusterState O m (N - m * k)) (c : ClusterState O m N) :
    (∃ h : IsAlphaState π c k z, alphaChild π c h = d) ↔
      ∃ b : Fin m → O, (∀ i, b i ∈ maximalIdeal O) ∧
        proj O m (N - m * k) b = d.1 ∧
        c.1 = proj O m N (alphaParentCoeff π b k (resSect O z)) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  constructor
  · rintro ⟨h, hd⟩
    have ha : proj O m N (classSect O m N c.1) = c.1 := proj_classSect O m N c.1
    obtain ⟨b, hbmem, hbfac, hbproj⟩ :=
      alphaChild_spec hπ hm hN c h (classSect O m N c.1) ha
    have hfa : monicPoly (classSect O m N c.1) = alphaParent π b k (resSect O z) := by
      refine comp_recentre_injective (pow_ne_zero k hπ0) (resSect O z) ?_
      rw [hbfac, alphaParent_recentre]
    refine ⟨b, hbmem, ?_, ?_⟩
    · rw [hbproj, hd]
    · rw [← ha]
      congr 1
      funext i
      exact coeff_eq_of_monicPoly_eq_alphaParent hfa i
  · rintro ⟨b, hbmem, hbproj, hc⟩
    obtain ⟨h, hch⟩ := exists_isAlphaState_of_alphaParent hπ hm hN hk hw hz hbmem
      (monicPoly_alphaParentCoeff π b k (resSect O z)) hc
    exact ⟨h, Subtype.ext (hch.trans hbproj)⟩

/-! ## 5. A section of the level-`n` truncation -/

/-- A set-theoretic section of `O → O ⧸ 𝔪 ^ n` — the digit chooser the fibre count enumerates
over.  (`resSect` is the `n = 1` analogue with the residue field written as such.) -/
noncomputable def resPowSect (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n : ℕ) : Res O n → O :=
  Function.surjInv Ideal.Quotient.mk_surjective

theorem mk_resPowSect (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n : ℕ) (x : Res O n) :
    Ideal.Quotient.mk ((maximalIdeal O) ^ n) (resPowSect O n x) = x :=
  Function.surjInv_eq _ x

end Fibre

/-! ## 6. H.115 (clause iii) — the fibre count -/

/-- **H.115 (clause iii).** Every ghost fibre has cardinality `Q ^ (k · c(m))`,
`c(m) = clusterC m = m (m − 1) / 2` (the R2 unit-pivot mechanism, H.60).

The bijection enumerated is `u ↦` the state carried by `alphaParentCoeff π (b₀ + π ^ (N − m k) û)`
where `b₀` is one fixed lift of the child and `û` is the digit vector `u` lifted coordinatewise;
`proj_alphaParentCoeff_eq_iff` says precisely that coordinate `j` is read modulo `π ^ (k j)`. -/
theorem card_alphaFiber {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] {π : O} (hπ : Irreducible π) {m N k : ℕ}
    {z : ResidueField O} (hm : 2 ≤ m) (hN : 1 ≤ N) (hk : 1 ≤ k) (hw : m * k ≤ N - 1)
    (hz : z ≠ 0) (d : ClusterState O m (N - m * k)) :
    Nat.card {c : ClusterState O m N | ∃ h : IsAlphaState π c k z, alphaChild π c h = d}
      = residueCard O ^ (k * clusterC m) := by
  classical
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hm1 : 1 ≤ m := by omega
  have hmkN : m * k ≤ N := by omega
  have hW1 : 1 ≤ N - m * k := by omega
  -- one fixed lift of the child, with coordinates in `𝔪`
  have hlift : ∀ i : Fin m, ∃ y : O, y ∈ maximalIdeal O ∧
      Ideal.Quotient.mk ((maximalIdeal O) ^ (N - m * k)) y = d.1 i := fun i =>
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (d.2 i)
  choose b₀ hb₀mem hb₀d using hlift
  have hb₀proj : proj O m (N - m * k) b₀ = d.1 := funext hb₀d
  -- the shifted lift attached to a digit vector
  have hshiftmem : ∀ (x : O), π ^ (N - m * k) * x ∈ maximalIdeal O := by
    intro x
    have hdvd : π ∣ π ^ (N - m * k) * x :=
      Dvd.dvd.mul_right (dvd_pow_self π (by omega)) x
    have h := (mem_maximalIdeal_pow_iff_dvd_of_irr hπ 1 (π ^ (N - m * k) * x)).2 (by rwa [pow_one])
    rwa [pow_one] at h
  have hbmem : ∀ (u : (j : Fin m) → Res O (k * (j : ℕ))) (i : Fin m),
      b₀ i + π ^ (N - m * k) * resPowSect O (k * (i : ℕ)) (u i) ∈ maximalIdeal O := fun u i =>
    Ideal.add_mem _ (hb₀mem i) (hshiftmem _)
  have hbproj : ∀ u : (j : Fin m) → Res O (k * (j : ℕ)),
      proj O m (N - m * k) (fun j => b₀ j + π ^ (N - m * k) * resPowSect O (k * (j : ℕ)) (u j))
        = d.1 := by
    intro u
    rw [← hb₀proj, proj_eq_iff_pow_dvd hπ]
    intro j
    exact ⟨resPowSect O (k * (j : ℕ)) (u j), by ring⟩
  -- the state carried by a lift
  have hstate : ∀ b : Fin m → O, ∀ i,
      proj O m N (alphaParentCoeff π b k (resSect O z)) i
        ∈ (maximalIdeal O).map (Ideal.Quotient.mk ((maximalIdeal O) ^ N)) := by
    intro b i
    exact Ideal.mem_map_of_mem _ (mem_maximalIdeal_of_monicPoly_eq_alphaParent hπ hk
      (monicPoly_alphaParentCoeff π b k (resSect O z)) i)
  -- the enumeration
  set Θ : ((j : Fin m) → Res O (k * (j : ℕ))) →
      {c : ClusterState O m N | ∃ h : IsAlphaState π c k z, alphaChild π c h = d} :=
    fun u => ⟨⟨proj O m N (alphaParentCoeff π
        (fun j => b₀ j + π ^ (N - m * k) * resPowSect O (k * (j : ℕ)) (u j)) k (resSect O z)),
        hstate _⟩,
      (mem_alphaFiber_iff hπ hm hN hk hw hz d _).2
        ⟨_, hbmem u, hbproj u, rfl⟩⟩ with hΘ
  have hbij : Function.Bijective Θ := by
    constructor
    · intro u u' huu
      have h1 : proj O m N (alphaParentCoeff π
            (fun j => b₀ j + π ^ (N - m * k) * resPowSect O (k * (j : ℕ)) (u j)) k (resSect O z))
          = proj O m N (alphaParentCoeff π
            (fun j => b₀ j + π ^ (N - m * k) * resPowSect O (k * (j : ℕ)) (u' j)) k
              (resSect O z)) :=
        congrArg (fun x => x.1.1) huu
      have h2 := (proj_alphaParentCoeff_eq_iff hπ hm1 hmkN (resSect O z) _ _).1 h1
      funext j
      have h3 := h2 j
      have h4 : (b₀ j + π ^ (N - m * k) * resPowSect O (k * (j : ℕ)) (u j))
          - (b₀ j + π ^ (N - m * k) * resPowSect O (k * (j : ℕ)) (u' j))
          = π ^ (N - m * k) *
            (resPowSect O (k * (j : ℕ)) (u j) - resPowSect O (k * (j : ℕ)) (u' j)) := by ring
      rw [h4, pow_add] at h3
      have h5 := (mul_dvd_mul_iff_left (pow_ne_zero (N - m * k) hπ0)).1 h3
      have h6 := Ideal.Quotient.eq.2
        ((mem_maximalIdeal_pow_iff_dvd_of_irr hπ (k * (j : ℕ)) _).2 h5)
      rw [mk_resPowSect, mk_resPowSect] at h6
      exact h6
    · rintro ⟨c, hcS⟩
      obtain ⟨b, hbm, hbd, hcb⟩ := (mem_alphaFiber_iff hπ hm hN hk hw hz d c).1 hcS
      have hdiff : ∀ j : Fin m, π ^ (N - m * k) ∣ (b j - b₀ j) := by
        have := (proj_eq_iff_pow_dvd hπ (N := N - m * k) b b₀).1 (hbd.trans hb₀proj.symm)
        exact this
      refine ⟨fun j => Ideal.Quotient.mk ((maximalIdeal O) ^ (k * (j : ℕ)))
        (divPow π (N - m * k) (b j - b₀ j)), ?_⟩
      refine Subtype.ext (Subtype.ext ?_)
      rw [hcb]
      refine (proj_alphaParentCoeff_eq_iff hπ hm1 hmkN (resSect O z) _ _).2 ?_
      intro j
      have hbj : b j = b₀ j + π ^ (N - m * k) * divPow π (N - m * k) (b j - b₀ j) := by
        have := divPow_spec (hdiff j)
        linear_combination this
      have hmk' : Ideal.Quotient.mk ((maximalIdeal O) ^ (k * (j : ℕ)))
          (resPowSect O (k * (j : ℕ)) (Ideal.Quotient.mk ((maximalIdeal O) ^ (k * (j : ℕ)))
            (divPow π (N - m * k) (b j - b₀ j))))
          = Ideal.Quotient.mk ((maximalIdeal O) ^ (k * (j : ℕ)))
            (divPow π (N - m * k) (b j - b₀ j)) := mk_resPowSect _ _ _
      have hd2 : π ^ (k * (j : ℕ)) ∣
          (resPowSect O (k * (j : ℕ)) (Ideal.Quotient.mk ((maximalIdeal O) ^ (k * (j : ℕ)))
            (divPow π (N - m * k) (b j - b₀ j))) - divPow π (N - m * k) (b j - b₀ j)) :=
        (mem_maximalIdeal_pow_iff_dvd_of_irr hπ (k * (j : ℕ)) _).1 (Ideal.Quotient.eq.1 hmk')
      obtain ⟨s, hs⟩ := hd2
      refine ⟨s, ?_⟩
      rw [hbj, pow_add]
      linear_combination (π ^ (N - m * k)) * hs
  -- the count
  have hcard : Nat.card ((j : Fin m) → Res O (k * (j : ℕ)))
      = Nat.card {c : ClusterState O m N | ∃ h : IsAlphaState π c k z, alphaChild π c h = d} :=
    Nat.card_eq_of_bijective Θ hbij
  rw [← hcard, Nat.card_pi]
  simp only [card_res]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => i) m, Finset.sum_range_id,
    clusterC, Nat.choose_two_right]

end Uniformity.Density.Induction

/-! ## 7. Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Induction.pow_dvd_coeff_comp_X_add_C
#print axioms Uniformity.Density.Induction.comp_recentre_injective
#print axioms Uniformity.Density.Induction.proj_eq_iff_pow_dvd
#print axioms Uniformity.Density.Induction.alphaParentCoeff
#print axioms Uniformity.Density.Induction.monicPoly_alphaParentCoeff
#print axioms Uniformity.Density.Induction.proj_alphaParentCoeff_eq_iff
#print axioms Uniformity.Density.Induction.mem_alphaFiber_iff
#print axioms Uniformity.Density.Induction.resPowSect
#print axioms Uniformity.Density.Induction.card_alphaFiber

end AxCheck

/-! ## 8. TEETH — the fibre exponent as a product of coordinate windows

The battery's `P1(d)` measures, per `(k, z)` slice, the size of every α fibre.  The theorem's
closed form is `Q ^ (k · c(m))`; the enumeration form is the product over coordinates
`∏_{j < m} Q ^ (k j)` — coordinate `j` of the parent forgets exactly `k · j` digits.  The plan
is the battery's own `part1` plan crossed with its realized slopes. -/

section NumericFibre

private def fibreCN (m : ℕ) : ℕ := m * (m - 1) / 2

private def fibrePlan : List (ℕ × ℕ × ℕ) :=
  [(2, 2, 6), (2, 3, 6), (2, 4, 4), (3, 2, 5), (3, 3, 4), (3, 4, 3)]

private def fibreK (m N : ℕ) : List ℕ :=
  (List.range (N + 1)).filter fun k => decide (1 ≤ k ∧ m * k ≤ N - 1)

-- closed form = product of the per-coordinate windows, at every realized slope
#guard fibrePlan.all fun p =>
  (fibreK p.2.1 p.2.2).all fun k =>
    p.1 ^ (k * fibreCN p.2.1)
      == ((List.range p.2.1).map fun j => p.1 ^ (k * j)).foldl (· * ·) 1

-- `clusterC m = m.choose 2` is the exponent slope the theorem states
#guard (List.range 8).all fun m => fibreCN m == Nat.choose m 2

-- the two largest live slices of the battery, on the nose
#guard (fibreK 3 6, 2 ^ (1 * fibreCN 3)) == ([1], 8)
#guard (fibreK 2 6, 2 ^ (2 * fibreCN 2)) == ([1, 2], 4)

end NumericFibre
