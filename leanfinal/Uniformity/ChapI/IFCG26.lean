/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG24
import Uniformity.ChapI.IFCG25
import Uniformity.ChapB.B42

/-!
# Uniformity.ChapI.IFCG26 — [CRL 2026-08-30] general-position fractional faces and the
mass-3 remainder law

Stage CRL of the cone census (design record `runs/wave-c/verdict_CRL.md`).  CN2 (`IFCG23`)
proved the class-level decidedness criterion at the PURE fractional face and left §7's
`FracFaceForcesRamStatement` (the general-position face) open; CN4 (`IFCG24`) named the
exact open residue `ConeRemainderLaw (m, σ)`; CN5 (`IFCG25`) rebased the census so the
family is consumed at EVERY `e ≥ 3` (`e = 2` closed there).  This file:

* **§1 the general-position bridge** (Lean-core): every class-NP abscissa attained
  strictly below the frame floor is `OnSide` for EVERY lift, and every lift's `suppVal`
  equals the class support — CN2's purity bridge freed from the endpoint-spanning
  hypothesis.
* **§2 the Hensel heart** (consumes the SIGNED gate-(b) cite
  `Uniformity.Density.Leaf.exists_slope_factorization` = B.42, GN15 Thm 2.3 + FGMN
  Thm 6.6 at the x-frame): a two-point side of slope `−u/ℓ` of a monic `f` with
  `f̄ = X̄^deg` splits off a monic `(u,ℓ)`-pure factor of positive degree.  The
  `f(0) = 0` corner is handled by an X-strip induction (`divX`), not by hypothesis.
* **§3 ★ `fracFaceForcesRam_of_stratum`**: the general-position fractional-face forcing
  at the census carrier — a visible class NP face of slope `h/e'` (`e' ≥ 2`, coprime)
  ANYWHERE on the polygon of a stratum class forces a monic irreducible factor with
  `e' ∣ ramIndexOf` in every lift.  This is IFCG23 §7's open statement restricted to the
  stratum `f̄ = X̄^m` (the census's carrier); the off-stratum general statement needs the
  unit-part Hensel coprime split at the x-frame, which neither the corpus nor mathlib has
  — the exact named residue.
* **§4 the unit-width decision**: a monic `(u,ℓ)`-pure polynomial (coprime, `u, ℓ > 0`)
  has `ℓ ∣ natDegree`, and at degree EXACTLY `ℓ` it is irreducible with
  `efPair = (ℓ, 1)` — the workhorse that decides every unit-width face block.
* **§5 ★★ `decidedAt_cubic_mixed`**: the mass-3 mixed classes (`v₀ ≥ 2`, `v₁ = 1`,
  `v₂ ≥ 1`) are DECIDED with type `{(1,1),(2,1)}` — the polygon has the width-1
  integer-slope block (linear factor) and the width-2 slope-`1/2` block (ramified
  quadratic), uniformly over the invisible corner `v₀` (including `a₀ = 0`).
* **§6 the mass-3 remainder carrier**: `(stratum ∩ shallow) \ pureFaceSet = mixedBox`
  at `m = 3`, with the exact count `#mixedBox = (q−1)·q^(3K−5)`.
* **§7 ★★★ `coneRemainderLaw_three`**: `ConeRemainderLaw 3 σ` for EVERY `σ` — the pair
  `(X − 1, X^5)` at the mixed type, `(0, 1)` otherwise — closing the census family's
  forced `e = 3` member; `zeroConeClause_three` fires the `m = 3` zero-cone clause.

## Axiom fence

§1 is Lean core.  §§2–7 consume exactly ONE extra axiom: the owner-signed gate-(b)
literature cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42; faithfulness
entry `blueprint/CHAP-I_capstone_conditionality.md`, DATED ADDENDUM 2026-08-16).  The
C.33 (r = 1) cites are NOT consumed; no ChapC import.  Zero sorries at landing.

## The honest fence (what stays open)

1. `FracFaceForcesRamStatement` (IFCG23 §7, arbitrary classes): open OFF the stratum —
   the missing leg is the x-frame unit-part Hensel split (`f̄ = X̄^μ·ū`, `ū(0) ≠ 0` ⇒
   compatible factorization of `f`).
2. `ConeRemainderLaw e σ` at `e ≥ 4`: open — the carrier's general-position sector needs
   the width bookkeeping of ALL class faces at once (this file's §1/§4 are the per-face
   engines), and the `e' < m` wide faces need the residual refinement (class-stable
   residual polynomials + the C133mh/`theoremA` bridge — FP1's GC0).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG26

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG17 (decidedAt_unique)
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport classNPSupport_le
  classCoeffVal_exact le_classCoeffVal_iff_dvd classCoeffVal_le exists_npAttains)
open Uniformity.Density.IFCG23 (addVal_eq_of_pow_dvd_not_dvd le_npHgt_monicPoly
  npHgt_monicPoly_eq npHgt_monicPoly_top dvd_ramIndexOf_of_isPure)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_qmonomial shallowSet
  mem_stratum_X_pow_iff card_setOf_le_resOrd card_setOf_resOrd_eq card_pi_set
  faceH faceBox pureFaceSet coneRemainderCount ConeRemainderLaw ZeroConeClause
  zeroConeClause_of_remainderLaw npHeight_coe)

attribute [local instance] Classical.propDecidable

/-! ## §0 — small supply: keys, side membership, linear factors, singleton factorizations -/

section Supply

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- On-side abscissae within the degree range are `sideSet` members. -/
theorem mem_sideSet_of_onSide {f : Polynomial O} {u ℓ j : ℕ}
    (hj : j ≤ f.natDegree) (h : OnSide X f u ℓ j) : j ∈ sideSet X f u ℓ := by
  classical
  simp only [sideSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, h⟩

/-- A monic polynomial of degree 1 over a domain is irreducible. -/
theorem irreducible_of_monic_natDegree_one {f : Polynomial O} (hf : f.Monic)
    (hd : f.natDegree = 1) : Irreducible f := by
  constructor
  · intro hunit
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  · intro a b hab
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hab
      exact hf.ne_zero hab
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hab
      exact hf.ne_zero hab
    have hdeg : a.natDegree + b.natDegree = 1 := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, hd]
    have hlead : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hab]
      exact hf
    rcases Nat.eq_zero_or_pos a.natDegree with hda | hda
    · left
      have haC : a = Polynomial.C (a.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hda
      have hulc : IsUnit a.leadingCoeff := IsUnit.of_mul_eq_one _ hlead
      rw [Polynomial.leadingCoeff, hda] at hulc
      rw [haC]
      exact Polynomial.isUnit_C.mpr hulc
    · right
      have hdb : b.natDegree = 0 := by omega
      have hbC : b = Polynomial.C (b.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdb
      have hulc : IsUnit b.leadingCoeff :=
        IsUnit.of_mul_eq_one _ (by rw [mul_comm] at hlead; exact hlead)
      rw [Polynomial.leadingCoeff, hdb] at hulc
      rw [hbC]
      exact Polynomial.isUnit_C.mpr hulc

/-- The monic factor multiset of a monic irreducible is the singleton. -/
theorem monicFactors_of_irreducible {f : Polynomial O} (hf : f.Monic)
    (hirr : Irreducible f) : monicFactors f = {f} := by
  refine monicFactors_eq ⟨?_, ?_⟩
  · intro g hg
    rw [Multiset.mem_singleton.mp hg]
    exact ⟨hf, hirr⟩
  · exact Multiset.prod_singleton f

/-- A monic polynomial of positive degree has a monic irreducible factor. -/
theorem exists_mem_monicFactors {f : Polynomial O} (hf : f.Monic)
    (hd : 0 < f.natDegree) : ∃ g', g' ∈ monicFactors f := by
  rcases Multiset.empty_or_exists_mem (monicFactors f) with h2 | h2
  · exfalso
    have hspec := monicFactors_spec hf
    have h3 : f.natDegree = 0 := by
      rw [← hspec.2, h2, Multiset.prod_zero]
      exact natDegree_one
    omega
  · exact h2

/-- `monicPoly 0 = X ^ m`, over ANY commutative ring (IFCG23's `monicPoly_zero` without
the DVR baggage — needed over `ResidueField O`). -/
theorem monicPoly_zero' {R : Type*} [CommRing R] (m : ℕ) :
    monicPoly (fun _ : Fin m => (0 : R)) = X ^ m := by
  unfold monicPoly
  simp

/-- The x-frame polygon height at a vanishing coefficient is `⊤`. -/
theorem npHgt_X_eq_top {f : Polynomial O} {j : ℕ} (h : f.coeff j = 0) :
    npHgt X f j = ⊤ := by
  show gaussVal (dev X f j) = ⊤
  rw [dev_X, h, Polynomial.C_0]
  exact gaussVal_eq_top_iff.2 rfl

end Supply

/-! ## §1 — the general-position bridge: visible attained abscissae are lift-`OnSide` -/

section Bridge

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The class support bounds every lift's support value from below (every abscissa, no
visibility needed). -/
theorem le_suppVal_monicPoly {π : O} (hπ : Irreducible π) {m N h e' : ℕ}
    {c : Coeff O m N} {a : Fin m → O} (ha : proj O m N a = c) :
    (classNPSupport c h e' : ℕ∞) ≤ suppVal X (monicPoly a) h e' := by
  rw [suppVal, monicPoly_natDegree]
  refine Finset.le_inf ?_
  intro j hj
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  rcases eq_or_lt_of_le hj with rfl | hjlt
  · rw [npHgt_monicPoly_top, smul_zero, zero_add]
    exact_mod_cast classNPSupport_le c h e'
  · have hcls : classNPSupport c h e' ≤ e' * classCoeffVal c ⟨j, hjlt⟩ + h * j := by
      have h3 := classNPSupport_le_apply c h e' (le_of_lt hjlt)
      unfold npHeight at h3
      rwa [dif_pos hjlt] at h3
    have hh := le_npHgt_monicPoly hπ ha hjlt
    calc (classNPSupport c h e' : ℕ∞)
        ≤ ((e' * classCoeffVal c ⟨j, hjlt⟩ + h * j : ℕ) : ℕ∞) := by exact_mod_cast hcls
      _ = e' • ((classCoeffVal c ⟨j, hjlt⟩ : ℕ) : ℕ∞) + ((h * j : ℕ) : ℕ∞) := by
          rw [nsmul_eq_mul]
          push_cast
          ring
      _ ≤ e' • npHgt X (monicPoly a) j + ((h * j : ℕ) : ℕ∞) := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          gcongr

-- `he'` is kept for signature honesty (the guard against the vacuous slope datum
-- `e' = 0`, exactly as in IFCG23's `isPure_monicPoly_of_face`) even though this proof
-- happens not to consume it.
set_option linter.unusedVariables false in
/-- ★ **The general-position bridge**: strictly below the frame floor, every class-NP
attained abscissa is `OnSide` for every lift, and the lift's support value IS the class
support.  (CN2's `isPure_monicPoly_of_face` freed from the endpoint-spanning hypothesis:
purity is the special case `i ∈ {0, m}`.) -/
theorem onSide_monicPoly_of_npAttains {π : O} (hπ : Irreducible π) {m N h e' : ℕ}
    (he' : 0 < e') {c : Coeff O m N} (hvis : NPVisibleAt c h e') {i : ℕ}
    (hi : NPAttains c h e' i) {a : Fin m → O} (ha : proj O m N a = c) :
    OnSide X (monicPoly a) h e' i ∧
      suppVal X (monicPoly a) h e' = (classNPSupport c h e' : ℕ∞) := by
  have him : i ≤ m := hi.1
  have hFi : e' • npHgt X (monicPoly a) i + ((h * i : ℕ) : ℕ∞)
      = (classNPSupport c h e' : ℕ∞) := by
    rcases eq_or_lt_of_le him with rfl | hilt
    · have h2 := hi.2
      have hnpm : npHeight c i = 0 := by
        unfold npHeight
        rw [dif_neg (lt_irrefl i)]
      rw [hnpm, Nat.mul_zero, Nat.zero_add] at h2
      rw [npHgt_monicPoly_top, smul_zero, zero_add]
      exact Nat.cast_inj.mpr h2
    · have h2 := hi.2
      have hnp : npHeight c i = classCoeffVal c ⟨i, hilt⟩ := by
        unfold npHeight
        rw [dif_pos hilt]
      rw [hnp] at h2
      have hvvis : classCoeffVal c ⟨i, hilt⟩ < N := by
        have hfl : classNPSupport c h e' < e' * N := hvis
        have h4 : e' * classCoeffVal c ⟨i, hilt⟩ < e' * N := by omega
        exact Nat.lt_of_mul_lt_mul_left h4
      rw [npHgt_monicPoly_eq hπ ha hilt hvvis, nsmul_eq_mul, ← Nat.cast_mul,
        ← Nat.cast_add]
      exact Nat.cast_inj.mpr h2
  have hle := le_suppVal_monicPoly (h := h) (e' := e') hπ ha
  have hsupple : suppVal X (monicPoly a) h e' ≤ (classNPSupport c h e' : ℕ∞) := by
    rw [← hFi, suppVal, monicPoly_natDegree]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  have hsupp : suppVal X (monicPoly a) h e' = (classNPSupport c h e' : ℕ∞) :=
    le_antisymm hsupple hle
  refine ⟨?_, hsupp⟩
  show e' • npHgt X (monicPoly a) i + ((h * i : ℕ) : ℕ∞) = suppVal X (monicPoly a) h e'
  rw [hsupp]
  exact hFi

end Bridge

/-! ## §2 — the Hensel heart: a two-point side splits off a pure factor

Consumes the signed B.42 cite `exists_slope_factorization` (x-frame instance).  The
`f(0) = 0` corner is handled by stripping `X` (`divX`) and inducting on the degree. -/

section Heart

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem exists_pure_factor_aux [IsAdicComplete (maximalIdeal O) O]
    {π : O} (hπ : Irreducible π) (n : ℕ) :
    ∀ f : Polynomial O, f.natDegree ≤ n → f.Monic →
      f.map (residue O) = X ^ f.natDegree →
      ∀ u ℓ i j : ℕ, 0 < u → 0 < ℓ → Nat.Coprime u ℓ → i < j → j ≤ f.natDegree →
      OnSide X f u ℓ i → OnSide X f u ℓ j → suppVal X f u ℓ ≠ ⊤ →
      ∃ F R : Polynomial O, F.Monic ∧ R.Monic ∧ IsPure X F u ℓ ∧
        0 < F.natDegree ∧ f = F * R := by
  induction n with
  | zero =>
      intro f hfn hf hres u ℓ i j hu hℓ hcop hij hjd hOi hOj htop
      omega
  | succ n ih =>
      intro f hfn hf hres u ℓ i j hu hℓ hcop hij hjd hOi hOj htop
      by_cases h0 : f.coeff 0 = 0
      · -- THE X-STRIP: `f = f.divX * X`; transfer the side down one abscissa and recurse.
        set f₁ := f.divX with hf₁def
        have heq : f₁ * X = f := by
          have h2 := Polynomial.divX_mul_X_add f
          rwa [h0, Polynomial.C_0, add_zero] at h2
        have hfne : f ≠ 0 := hf.ne_zero
        have hf₁ne : f₁ ≠ 0 := by
          rintro h1
          rw [h1, zero_mul] at heq
          exact hfne heq.symm
        have hdeg : f.natDegree = f₁.natDegree + 1 := by
          rw [← heq, Polynomial.natDegree_mul hf₁ne Polynomial.X_ne_zero,
            Polynomial.natDegree_X]
        have hf₁m : f₁.Monic := by
          have h2 : f₁.leadingCoeff * (X : Polynomial O).leadingCoeff = f.leadingCoeff := by
            rw [← Polynomial.leadingCoeff_mul, heq]
          rw [Polynomial.leadingCoeff_X, mul_one] at h2
          exact h2.trans hf
        have hres₁ : f₁.map (residue O) = X ^ f₁.natDegree := by
          have h2 : (f₁.map (residue O)) * (X : Polynomial (ResidueField O))
              = f.map (residue O) := by
            rw [← Polynomial.map_X (f := residue O), ← Polynomial.map_mul, heq]
          have h3 : (f₁.map (residue O)) * (X : Polynomial (ResidueField O))
              = X ^ f₁.natDegree * X := by
            rw [h2, hres, hdeg, pow_succ]
          exact mul_right_cancel₀ Polynomial.X_ne_zero h3
        have hnpg : ∀ t : ℕ, npHgt X f (t + 1) = npHgt X f₁ t := by
          intro t
          rw [npHgt_X, npHgt_X, Polynomial.coeff_divX]
        have hFval : ∀ t : ℕ, ℓ • npHgt X f (t + 1) + ((u * (t + 1) : ℕ) : ℕ∞)
            = (ℓ • npHgt X f₁ t + ((u * t : ℕ) : ℕ∞)) + (u : ℕ∞) := by
          intro t
          rw [hnpg t, Nat.mul_succ, Nat.cast_add, add_assoc]
        have hSf : suppVal X f u ℓ = (Finset.range (f.natDegree + 1)).inf
            (fun t => ℓ • npHgt X f t + ((u * t : ℕ) : ℕ∞)) := rfl
        have hSf₁ : suppVal X f₁ u ℓ = (Finset.range (f₁.natDegree + 1)).inf
            (fun t => ℓ • npHgt X f₁ t + ((u * t : ℕ) : ℕ∞)) := rfl
        have hsupp : suppVal X f u ℓ = suppVal X f₁ u ℓ + (u : ℕ∞) := by
          refine le_antisymm ?_ ?_
          · obtain ⟨t₀, ht₀mem, ht₀⟩ := Finset.exists_mem_eq_inf
              (Finset.range (f₁.natDegree + 1))
              (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _))
              (fun t => ℓ • npHgt X f₁ t + ((u * t : ℕ) : ℕ∞))
            rw [Finset.mem_range, Nat.lt_succ_iff] at ht₀mem
            have h5 : suppVal X f u ℓ
                ≤ ℓ • npHgt X f (t₀ + 1) + ((u * (t₀ + 1) : ℕ) : ℕ∞) := by
              rw [hSf]
              exact Finset.inf_le (Finset.mem_range.mpr (by omega))
            rw [hFval t₀] at h5
            rw [hSf₁, ht₀]
            exact h5
          · rw [hSf]
            refine Finset.le_inf ?_
            intro t ht
            rw [Finset.mem_range, Nat.lt_succ_iff] at ht
            rcases Nat.eq_zero_or_pos t with rfl | htpos
            · rw [npHgt_X_eq_top h0, nsmul_eq_mul,
                ENat.mul_top (by exact_mod_cast hℓ.ne' : (ℓ : ℕ∞) ≠ 0), top_add]
              exact le_top
            · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
              rw [hFval t']
              have h7 : suppVal X f₁ u ℓ ≤ ℓ • npHgt X f₁ t' + ((u * t' : ℕ) : ℕ∞) := by
                rw [hSf₁]
                exact Finset.inf_le (Finset.mem_range.mpr (by omega))
              exact add_le_add h7 le_rfl
        have hipos : 1 ≤ i := by
          rcases Nat.eq_zero_or_pos i with rfl | h1i
          swap
          · exact h1i
          exfalso
          have h9 : ℓ • npHgt X f 0 + ((u * 0 : ℕ) : ℕ∞) = suppVal X f u ℓ := hOi
          rw [npHgt_X_eq_top h0, nsmul_eq_mul,
            ENat.mul_top (by exact_mod_cast hℓ.ne' : (ℓ : ℕ∞) ≠ 0), top_add] at h9
          exact htop h9.symm
        have htop₁ : suppVal X f₁ u ℓ ≠ ⊤ := by
          intro h11
          rw [h11, top_add] at hsupp
          exact htop hsupp
        have honside : ∀ t : ℕ, OnSide X f u ℓ (t + 1) → OnSide X f₁ u ℓ t := by
          intro t hOt
          have h9 : ℓ • npHgt X f (t + 1) + ((u * (t + 1) : ℕ) : ℕ∞)
              = suppVal X f u ℓ := hOt
          rw [hFval t, hsupp] at h9
          exact WithTop.add_right_cancel (ENat.coe_ne_top u) h9
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        obtain ⟨F, R, hFm, hRm, hFp, hFd, heqFR⟩ :=
          ih f₁ (by omega) hf₁m hres₁ u ℓ i' j' hu hℓ hcop (by omega) (by omega)
            (honside i' hOi) (honside j' hOj) htop₁
        refine ⟨F, R * X, hFm, hRm.mul Polynomial.monic_X, hFp, hFd, ?_⟩
        rw [← heq, heqFR, mul_assoc]
      · -- THE B.42 BRANCH: the signed slope dissection fires at `f(0) ≠ 0`.
        have hdeg0 : 0 < f.natDegree := by omega
        have hdev : dev X f 0 ≠ 0 := by
          rw [dev_X]
          intro hC
          exact h0 (by simpa using hC)
        obtain ⟨s, F, hs1, hs2, hs3, hprod, hs5, hs6⟩ :=
          exists_slope_factorization (μ := f.natDegree) hπ isKey_X hf hdeg0
            (by rw [Polynomial.map_X]; exact hres) hdev
        have hmem : (u, ℓ) ∈ s := by
          refine (hs5 u ℓ hℓ hcop).1 ?_
          exact Finset.one_lt_card.mpr
            ⟨i, mem_sideSet_of_onSide (by omega) hOi,
             j, mem_sideSet_of_onSide hjd hOj, by omega⟩
        obtain ⟨hFm, hFpure, _, _, hFdpos⟩ := hs3 (u, ℓ) hmem
        refine ⟨F (u, ℓ), ∏ p ∈ s.erase (u, ℓ), F p, hFm, ?_, hFpure, hFdpos, ?_⟩
        · exact Polynomial.monic_prod_of_monic _ _
            (fun p hp => (hs3 p (Finset.mem_of_mem_erase hp)).1)
        · rw [hprod, ← Finset.mul_prod_erase s F hmem]

/-- ★ **The two-point side splits off a pure factor** (the x-frame face factorization,
packaged): over a complete DVR, a monic `f` with `f̄ = X̄^deg f` whose x-polygon has a
side of slope `−u/ℓ` (coprime, `u, ℓ > 0`) attained at two abscissae factors as
`f = F · R` with `F` monic `(u,ℓ)`-pure of positive degree and `R` monic.  Consumes the
signed B.42 cite; the `f(0) = 0` corner is an X-strip induction, not a hypothesis. -/
theorem exists_pure_factor_of_two_point_side [IsAdicComplete (maximalIdeal O) O]
    {π : O} (hπ : Irreducible π) {f : Polynomial O} (hf : f.Monic)
    (hres : f.map (residue O) = X ^ f.natDegree)
    {u ℓ i j : ℕ} (hu : 0 < u) (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hij : i < j) (hjd : j ≤ f.natDegree)
    (hOi : OnSide X f u ℓ i) (hOj : OnSide X f u ℓ j)
    (htop : suppVal X f u ℓ ≠ ⊤) :
    ∃ F R : Polynomial O, F.Monic ∧ R.Monic ∧ IsPure X F u ℓ ∧
      0 < F.natDegree ∧ f = F * R :=
  exists_pure_factor_aux hπ f.natDegree f le_rfl hf hres u ℓ i j hu hℓ hcop hij hjd
    hOi hOj htop

end Heart

/-! ## §3 — ★ the general-position forcing at the census carrier -/

section Forcing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **CRL — the general-position fractional-face forcing, stratum instance** (IFCG23
§7's `FracFaceForcesRamStatement` restricted to the census carrier `f̄ = X̄^m`): a
visible class NP face of slope `h/e'` (`e' ≥ 2`, `gcd(h,e') = 1`) ANYWHERE on the
polygon of a stratum class forces, in EVERY lift, a monic irreducible factor with
`e' ∣ ramIndexOf`.  The off-stratum statement is the named residue (unit-part Hensel
split). -/
theorem fracFaceForcesRam_of_stratum {m N h e' : ℕ} (he' : 2 ≤ e')
    (hcop : Nat.Coprime h e') {c : Coeff O m N}
    (hstr : c ∈ levelZeroStratum O m N (X ^ m))
    (hface : ClassNPFace c h e') (hvis : NPVisibleAt c h e')
    {a : Fin m → O} (ha : proj O m N a = c) :
    ∃ g' ∈ monicFactors (monicPoly a), e' ∣ ramIndexOf g' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨i, j, hij, hAi, hAj⟩ := hface
  have hu : 0 < h := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · exfalso
      have h1 : e' = 1 := by
        have h2 := hcop
        rwa [Nat.coprime_zero_left] at h2
      omega
    · exact hh
  have he'0 : 0 < e' := by omega
  obtain ⟨hOi, hsupp⟩ := onSide_monicPoly_of_npAttains hπ he'0 hvis hAi ha
  obtain ⟨hOj, -⟩ := onSide_monicPoly_of_npAttains hπ he'0 hvis hAj ha
  have htop : suppVal X (monicPoly a) h e' ≠ ⊤ := by
    rw [hsupp]
    exact ENat.coe_ne_top _
  have hres : (monicPoly a).map (residue O) = X ^ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree]
    exact hstr a ha
  obtain ⟨F, R, hFm, hRm, hFp, hFd, heqFR⟩ :=
    exists_pure_factor_of_two_point_side hπ (monicPoly_monic a) hres hu he'0 hcop hij
      (by rw [monicPoly_natDegree]; exact hAj.1) hOi hOj htop
  obtain ⟨g', hg'⟩ := exists_mem_monicFactors hFm hFd
  refine ⟨g', ?_, dvd_ramIndexOf_of_isPure hπ he'0 hcop hFm hFp hg'⟩
  rw [heqFR, monicFactors_mul hFm hRm]
  exact Multiset.mem_add.mpr (Or.inl hg')

end Forcing

/-! ## §4 — the unit-width decision -/

section UnitWidth

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The slope denominator divides the degree of every monic pure polynomial (each monic
irreducible factor has `ℓ ∣ ramIndexOf ∣ natDegree`; degrees add). -/
theorem dvd_natDegree_of_isPure {π : O} (hπ : Irreducible π) {F : Polynomial O}
    (hF : F.Monic) {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hpure : IsPure X F u ℓ) : ℓ ∣ F.natDegree := by
  have hspec := monicFactors_spec hF
  have hdeg : F.natDegree = ((monicFactors F).map Polynomial.natDegree).sum := by
    conv_lhs => rw [← hspec.2]
    exact Polynomial.natDegree_multiset_prod_of_monic _ (fun p hp => (hspec.1 p hp).1)
  rw [hdeg]
  refine Multiset.dvd_sum ?_
  intro d hd
  rw [Multiset.mem_map] at hd
  obtain ⟨g', hg', rfl⟩ := hd
  have h1 : ℓ ∣ ramIndexOf g' := dvd_ramIndexOf_of_isPure hπ hℓ hcop hF hpure hg'
  have hg'm := (hspec.1 g' hg').1
  have hg'pos : 0 < g'.natDegree := natDegree_pos_of_mem_monicFactors hF hg'
  have h2 : ramIndexOf g' * inertiaDegOf g' = g'.natDegree :=
    ramIndexOf_mul_inertiaDegOf hg'm hg'pos
  exact h1.trans ⟨inertiaDegOf g', h2.symm⟩

/-- ★ **The unit-width block decision**: a monic `(u,ℓ)`-pure polynomial of degree
EXACTLY `ℓ` (coprime slope data) is irreducible, totally ramified of index `ℓ`:
`efPair = (ℓ, 1)`. -/
theorem irreducible_of_isPure_natDegree_eq {π : O} (hπ : Irreducible π)
    {F : Polynomial O} (hF : F.Monic) {u ℓ : ℕ} (hℓ : 0 < ℓ)
    (hcop : Nat.Coprime u ℓ) (hpure : IsPure X F u ℓ) (hdeg : F.natDegree = ℓ) :
    Irreducible F ∧ efPair F = (ℓ, 1) := by
  have hspec := monicFactors_spec hF
  obtain ⟨g', hg'⟩ := exists_mem_monicFactors hF (by omega)
  have hg'm := (hspec.1 g' hg').1
  have hg'irr := (hspec.1 g' hg').2
  have hg'pos : 0 < g'.natDegree := natDegree_pos_of_mem_monicFactors hF hg'
  have hram : ℓ ∣ ramIndexOf g' := dvd_ramIndexOf_of_isPure hπ hℓ hcop hF hpure hg'
  have hmul : ramIndexOf g' * inertiaDegOf g' = g'.natDegree :=
    ramIndexOf_mul_inertiaDegOf hg'm hg'pos
  have hinpos : 0 < inertiaDegOf g' := inertiaDegOf_pos (normValues_nonempty hg'm hg'pos)
  have hrampos : 0 < ramIndexOf g' := by
    rcases Nat.eq_zero_or_pos (ramIndexOf g') with h1 | h1
    · rw [h1, zero_mul] at hmul
      omega
    · exact h1
  have hramge : ℓ ≤ ramIndexOf g' := Nat.le_of_dvd hrampos hram
  have hg'ge : ℓ ≤ g'.natDegree := by
    have h3 : ramIndexOf g' ≤ ramIndexOf g' * inertiaDegOf g' :=
      Nat.le_mul_of_pos_right _ hinpos
    omega
  have hdegs : F.natDegree = ((monicFactors F).map Polynomial.natDegree).sum := by
    conv_lhs => rw [← hspec.2]
    exact Polynomial.natDegree_multiset_prod_of_monic _ (fun p hp => (hspec.1 p hp).1)
  obtain ⟨T, hT⟩ := Multiset.exists_cons_of_mem hg'
  have hsum : g'.natDegree + (T.map Polynomial.natDegree).sum = ℓ := by
    have h4 := hdegs
    rw [hT, Multiset.map_cons, Multiset.sum_cons, hdeg] at h4
    omega
  have hTzero : T = 0 := by
    by_contra hTne
    obtain ⟨g'', hg''⟩ := Multiset.exists_mem_of_ne_zero hTne
    have hg''mem : g'' ∈ monicFactors F := by
      rw [hT]
      exact Multiset.mem_cons_of_mem hg''
    have hg''pos : 0 < g''.natDegree := natDegree_pos_of_mem_monicFactors hF hg''mem
    have h8 : g''.natDegree ≤ (T.map Polynomial.natDegree).sum :=
      Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
        (Multiset.mem_map_of_mem _ hg'')
    omega
  have hFg : F = g' := by
    have h9 := hspec.2
    rw [hT, hTzero, Multiset.prod_cons, Multiset.prod_zero, mul_one] at h9
    exact h9.symm
  have hg'deg : g'.natDegree = ℓ := by
    rw [hTzero] at hsum
    simpa using hsum
  have hramle : ramIndexOf g' ≤ ℓ := by
    have h3 : ramIndexOf g' ≤ ramIndexOf g' * inertiaDegOf g' :=
      Nat.le_mul_of_pos_right _ hinpos
    omega
  have hrameq : ramIndexOf g' = ℓ := le_antisymm hramle hramge
  have hineq : inertiaDegOf g' = 1 := by
    rw [hrameq, hg'deg] at hmul
    exact Nat.eq_of_mul_eq_mul_left hℓ (by rw [hmul, mul_one])
  refine ⟨hFg ▸ hg'irr, ?_⟩
  rw [hFg]
  unfold efPair
  rw [hrameq, hineq]

end UnitWidth

/-! ## §5 — ★★ the mass-3 mixed decision -/

section CubicMixed

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The mixed cubic type: one split linear factor, one ramified quadratic. -/
def mixedType : FactorizationType := ⟨{(1, 1), (2, 1)}⟩

/-- Shared tail: a monic cubic split as (irreducible `(2,1)`-quadratic) × (monic linear)
has type `mixedType`. -/
private theorem typeOf_eq_of_split_two_one {f F R : Polynomial O}
    (hF : F.Monic) (hR : R.Monic) (hFirr : Irreducible F) (hFe : efPair F = (2, 1))
    (hRd : R.natDegree = 1) (heq : f = F * R) :
    typeOf f = mixedType := by
  have hRirr : Irreducible R := irreducible_of_monic_natDegree_one hR hRd
  have hdata : (typeOf f).data = ({(1, 1), (2, 1)} : Multiset (ℕ × ℕ)) := by
    rw [typeOf_data, heq, monicFactors_mul hF hR, monicFactors_of_irreducible hF hFirr,
      monicFactors_of_irreducible hR hRirr, Multiset.map_add, Multiset.map_singleton,
      Multiset.map_singleton, hFe, efPair_of_natDegree_one hR hRd]
    decide
  calc typeOf f = ⟨(typeOf f).data⟩ := rfl
    _ = ⟨({(1, 1), (2, 1)} : Multiset (ℕ × ℕ))⟩ := by rw [hdata]
    _ = mixedType := rfl

/-- ★★ **The mass-3 mixed classes are decided** (`v₀ ≥ 2`, `v₁ = 1`, `v₂ ≥ 1`): the
width-1 steep block is a linear factor and the width-2 slope-`1/2` face is a ramified
quadratic, uniformly over the invisible corner `v₀` (including lifts with `a₀ = 0`). -/
theorem decidedAt_cubic_mixed {K : ℕ} (hK : 1 < K) {c : Coeff O 3 K}
    (h0 : 2 ≤ classCoeffVal c 0) (h1 : classCoeffVal c 1 = 1)
    (h2 : 1 ≤ classCoeffVal c 2) :
    DecidedAt O 3 mixedType K c := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  intro a ha
  -- STEP 1: the class polygon at slope data `(1, 2)`: support `3`, attained at `1, 3`.
  have hnp0 : 2 ≤ npHeight c 0 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (0 : ℕ) < 3)]
    exact h0
  have hnp1 : npHeight c 1 = 1 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (1 : ℕ) < 3)]
    exact h1
  have hnp2 : 1 ≤ npHeight c 2 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (2 : ℕ) < 3)]
    exact h2
  have hnp3 : npHeight c 3 = 0 := by
    unfold npHeight
    rw [dif_neg (by norm_num : ¬ (3 : ℕ) < 3)]
  have hsup : classNPSupport c 1 2 = 3 := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h5 := classNPSupport_le_apply c 1 2 (show (1 : ℕ) ≤ 3 by norm_num)
      rw [hnp1] at h5
      omega
    · intro i hi
      interval_cases i
      · omega
      · rw [hnp1]
      · omega
      · rw [hnp3]
  have hA1 : NPAttains c 1 2 1 := ⟨by omega, by rw [hnp1, hsup]⟩
  have hA3 : NPAttains c 1 2 3 := ⟨le_refl 3, by rw [hnp3, hsup]⟩
  have hvis : NPVisibleAt c 1 2 := by
    show classNPSupport c 1 2 < 2 * K
    rw [hsup]
    omega
  -- STEP 2: the bridge — every lift is OnSide at `1` and `3`.
  obtain ⟨hO1, hsupf⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hA1 ha
  obtain ⟨hO3, -⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hA3 ha
  have htop : suppVal X (monicPoly a) 1 2 ≠ ⊤ := by
    rw [hsupf]
    exact ENat.coe_ne_top _
  -- STEP 3: the stratum reduction `f̄ = X̄³` (all class heights positive).
  have hres : (monicPoly a).map (residue O) = X ^ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree, map_monicPoly]
    have hzero : (fun i => residue O (a i)) = (fun _ : Fin 3 => (0 : ResidueField O)) := by
      funext i
      have h6 : 1 ≤ classCoeffVal c i := by
        fin_cases i
        · exact le_trans (by norm_num) h0
        · exact h1.ge
        · exact h2
      have h7 := (le_classCoeffVal_iff_dvd hπ (by omega : 1 ≤ K) ha i).1 h6
      rw [pow_one] at h7
      exact (IsLocalRing.residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hπ _).2 h7)
    rw [hzero, monicPoly_zero']
  -- STEP 4: the Hensel heart — split off the pure `(1,2)` factor.
  obtain ⟨F, R, hFm, hRm, hFp, hFd, heqFR⟩ :=
    exists_pure_factor_of_two_point_side hπ (monicPoly_monic a) hres one_pos two_pos
      (Nat.coprime_one_left 2) (by norm_num : (1 : ℕ) < 3) (monicPoly_natDegree a).ge
      hO1 hO3 htop
  -- STEP 5: degree bookkeeping — the pure block is the quadratic, the rest is linear.
  have h2dvd : 2 ∣ F.natDegree :=
    dvd_natDegree_of_isPure hπ hFm (by norm_num) (Nat.coprime_one_left 2) hFp
  have hdegsum : F.natDegree + R.natDegree = 3 := by
    have h6 := monicPoly_natDegree a
    rw [heqFR, Polynomial.natDegree_mul hFm.ne_zero hRm.ne_zero] at h6
    omega
  have hFdeg : F.natDegree = 2 := by omega
  have hRdeg : R.natDegree = 1 := by omega
  -- STEP 6: the unit-width decision + assembly.
  obtain ⟨hFirr, hFef⟩ := irreducible_of_isPure_natDegree_eq hπ hFm (by norm_num)
    (Nat.coprime_one_left 2) hFp hFdeg
  exact typeOf_eq_of_split_two_one hFm hRm hFirr hFef hRdeg heqFR

end CubicMixed

/-! ## §6 — the mass-3 remainder carrier and its count -/

section Carrier

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- The mass-3 mixed box: `v₀ ≥ 2`, `v₁ = 1`, `v₂ ≥ 1` (pi-set shape). -/
def mixedBox (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : ℕ) : Set (Coeff O 3 K) :=
  {c | ∀ i : Fin 3,
    c i ∈ (if (i : ℕ) = 0 then {x : Res O K | 2 ≤ resOrd x}
      else if (i : ℕ) = 1 then {x : Res O K | resOrd x = 1}
      else {x : Res O K | 1 ≤ resOrd x})}

theorem mem_mixedBox_iff {K : ℕ} (c : Coeff O 3 K) :
    c ∈ mixedBox O K ↔
      2 ≤ resOrd (c 0) ∧ resOrd (c 1) = 1 ∧ 1 ≤ resOrd (c 2) := by
  constructor
  · intro hc
    have h0' := hc 0
    have h1' := hc 1
    have h2' := hc 2
    rw [if_pos (show ((0 : Fin 3) : ℕ) = 0 from rfl)] at h0'
    rw [if_neg (show ¬ ((1 : Fin 3) : ℕ) = 0 by decide),
      if_pos (show ((1 : Fin 3) : ℕ) = 1 from rfl)] at h1'
    rw [if_neg (show ¬ ((2 : Fin 3) : ℕ) = 0 by decide),
      if_neg (show ¬ ((2 : Fin 3) : ℕ) = 1 by decide)] at h2'
    exact ⟨h0', h1', h2'⟩
  · rintro ⟨hA, hB, hC⟩ i
    by_cases hi0 : (i : ℕ) = 0
    · rw [if_pos hi0]
      have hieq : i = 0 := Fin.ext hi0
      rw [hieq]
      exact hA
    · rw [if_neg hi0]
      by_cases hi1 : (i : ℕ) = 1
      · rw [if_pos hi1]
        have hieq : i = 1 := Fin.ext hi1
        rw [hieq]
        exact hB
      · rw [if_neg hi1]
        have hieq : i = 2 := by
          have h5 := i.isLt
          exact Fin.ext (by omega)
        rw [hieq]
        exact hC

/-- ★ **The mass-3 remainder carrier**: outside the two pure-face boxes, the shallow
stratum is EXACTLY the mixed box. -/
theorem remainder_carrier_three {K : ℕ} (hK : 3 ≤ K) :
    ((levelZeroStratum O 3 K (X ^ 3) ∩ shallowSet O 3 K) \ pureFaceSet O 3 K)
      = mixedBox O K := by
  have hK1 : 1 ≤ K := by omega
  ext c
  have e0 : npHeight c 0 = resOrd (c 0) := by simpa using npHeight_coe c (0 : Fin 3)
  have e1 : npHeight c 1 = resOrd (c 1) := by simpa using npHeight_coe c (1 : Fin 3)
  have e2 : npHeight c 2 = resOrd (c 2) := by simpa using npHeight_coe c (2 : Fin 3)
  rw [mem_mixedBox_iff]
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hstr, hsh⟩, hnb⟩
    have hstr' := (mem_stratum_X_pow_iff hK1 c).1 hstr
    have hv0 : 1 ≤ resOrd (c 0) := hstr' 0
    have hv1 : 1 ≤ resOrd (c 1) := hstr' 1
    have hv2 : 1 ≤ resOrd (c 2) := hstr' 2
    have hshallow : resOrd (c 0) < 3 ∨ resOrd (c 1) < 2 := by
      obtain ⟨i, hi⟩ := hsh
      fin_cases i
      · exact Or.inl (by have hi' : resOrd (c 0) < 3 - 0 := hi; omega)
      · exact Or.inr (by have hi' : resOrd (c 1) < 3 - 1 := hi; omega)
      · exfalso
        have hi' : resOrd (c 2) < 3 - 2 := hi
        omega
    have hne1 : resOrd (c 0) ≠ 1 := by
      intro hv0eq
      refine hnb ⟨1, ?_, ?_, ?_⟩
      · show (1 : ℕ) ∈ faceH 3
        simp only [faceH, Finset.mem_filter, Finset.mem_range]
        exact ⟨by norm_num, by norm_num, Nat.coprime_one_left 3⟩
      · rw [e0]
        exact hv0eq
      · intro i
        fin_cases i
        · exact (show 1 * (3 - 0) ≤ 3 * npHeight c 0 by rw [e0]; omega)
        · exact (show 1 * (3 - 1) ≤ 3 * npHeight c 1 by rw [e1]; omega)
        · exact (show 1 * (3 - 2) ≤ 3 * npHeight c 2 by rw [e2]; omega)
    have hnot22 : ¬ (resOrd (c 0) = 2 ∧ 2 ≤ resOrd (c 1)) := by
      rintro ⟨hv0eq, hv1ge⟩
      refine hnb ⟨2, ?_, ?_, ?_⟩
      · show (2 : ℕ) ∈ faceH 3
        simp only [faceH, Finset.mem_filter, Finset.mem_range]
        exact ⟨by norm_num, by norm_num, by decide⟩
      · rw [e0]
        exact hv0eq
      · intro i
        fin_cases i
        · exact (show 2 * (3 - 0) ≤ 3 * npHeight c 0 by rw [e0]; omega)
        · exact (show 2 * (3 - 1) ≤ 3 * npHeight c 1 by rw [e1]; omega)
        · exact (show 2 * (3 - 2) ≤ 3 * npHeight c 2 by rw [e2]; omega)
    have hv0ge2 : 2 ≤ resOrd (c 0) := by omega
    have hv1eq : resOrd (c 1) = 1 := by
      by_contra hne
      have hv1ge2 : 2 ≤ resOrd (c 1) := by omega
      rcases hshallow with h5 | h5
      · exact hnot22 ⟨by omega, hv1ge2⟩
      · omega
    exact ⟨hv0ge2, hv1eq, hv2⟩
  · rintro ⟨hA, hB, hC⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine (mem_stratum_X_pow_iff hK1 c).2 ?_
      intro i
      fin_cases i
      · exact le_trans (by norm_num) hA
      · exact hB.ge
      · exact hC
    · exact ⟨1, show resOrd (c 1) < 3 - 1 by omega⟩
    · rintro ⟨h, hh, hc0, hcond⟩
      have hh2 : h < 3 ∧ (1 ≤ h ∧ Nat.Coprime h 3) := by
        have h5 := hh
        simp only [faceH, Finset.mem_filter, Finset.mem_range] at h5
        exact h5
      rw [e0] at hc0
      have hh' : h = 1 ∨ h = 2 := by omega
      rcases hh' with rfl | rfl
      · omega
      · have h4 : 2 * (3 - 1) ≤ 3 * npHeight c 1 := hcond 1
        rw [e1] at h4
        omega

/-- The mixed-box count: `(q−1)·q^(3K−5)`. -/
theorem card_mixedBox {K : ℕ} (hK : 3 ≤ K) :
    Nat.card (mixedBox O K : Set (Coeff O 3 K))
      = (residueCard O - 1) * residueCard O ^ (3 * K - 5) := by
  classical
  unfold mixedBox
  rw [card_pi_set, Fin.prod_univ_three]
  rw [if_pos (show ((0 : Fin 3) : ℕ) = 0 from rfl)]
  rw [if_neg (show ¬ ((1 : Fin 3) : ℕ) = 0 by decide),
    if_pos (show ((1 : Fin 3) : ℕ) = 1 from rfl)]
  rw [if_neg (show ¬ ((2 : Fin 3) : ℕ) = 0 by decide),
    if_neg (show ¬ ((2 : Fin 3) : ℕ) = 1 by decide)]
  rw [card_setOf_le_resOrd (show 2 ≤ K by omega),
    card_setOf_resOrd_eq (show 1 < K by omega),
    card_setOf_le_resOrd (show 1 ≤ K by omega)]
  rw [show K - 1 - 1 = K - 2 from by omega,
    show 3 * K - 5 = (K - 2) + (K - 2) + (K - 1) from by omega, pow_add, pow_add]
  ring

variable [IsAdicComplete (maximalIdeal O) O]

/-- ★ **The mass-3 remainder count at the mixed type** — the exact monomial, every
finite level. -/
theorem coneRemainderCount_three_mixed (M : ℕ) :
    coneRemainderCount O 3 mixedType M
      = (residueCard O - 1) * residueCard O ^ (3 * (M + 3) - 5) := by
  unfold coneRemainderCount
  have hK : 3 ≤ M + 3 := by omega
  have hassoc : ((decidedSet O 3 mixedType (M + 3)
        ∩ levelZeroStratum O 3 (M + 3) (X ^ 3) ∩ shallowSet O 3 (M + 3))
        \ pureFaceSet O 3 (M + 3))
      = decidedSet O 3 mixedType (M + 3)
        ∩ ((levelZeroStratum O 3 (M + 3) (X ^ 3) ∩ shallowSet O 3 (M + 3))
          \ pureFaceSet O 3 (M + 3)) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [hassoc, remainder_carrier_three hK]
  have hsub : mixedBox O (M + 3) ⊆ decidedSet O 3 mixedType (M + 3) := by
    intro c hc
    rw [mem_mixedBox_iff] at hc
    exact decidedAt_cubic_mixed (by omega) hc.1 hc.2.1 hc.2.2
  rw [Set.inter_eq_self_of_subset_right hsub]
  exact card_mixedBox hK

/-- At every other type the mass-3 remainder VANISHES. -/
theorem coneRemainderCount_three_ne {σ : FactorizationType} (hσ : σ ≠ mixedType)
    (M : ℕ) : coneRemainderCount O 3 σ M = 0 := by
  unfold coneRemainderCount
  have hK : 3 ≤ M + 3 := by omega
  have hassoc : ((decidedSet O 3 σ (M + 3)
        ∩ levelZeroStratum O 3 (M + 3) (X ^ 3) ∩ shallowSet O 3 (M + 3))
        \ pureFaceSet O 3 (M + 3))
      = decidedSet O 3 σ (M + 3)
        ∩ ((levelZeroStratum O 3 (M + 3) (X ^ 3) ∩ shallowSet O 3 (M + 3))
          \ pureFaceSet O 3 (M + 3)) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hempty : decidedSet O 3 σ (M + 3) ∩ mixedBox O (M + 3)
      = (∅ : Set (Coeff O 3 (M + 3))) := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hdec, hc⟩
    rw [mem_mixedBox_iff] at hc
    have hdec2 : DecidedAt O 3 mixedType (M + 3) c :=
      decidedAt_cubic_mixed (by omega) hc.1 hc.2.1 hc.2.2
    exact hσ (decidedAt_unique hdec hdec2)
  rw [hassoc, remainder_carrier_three hK, hempty]
  rw [Nat.card_coe_set_eq, Set.ncard_empty]

end Carrier

/-! ## §7 — ★★★ the mass-3 remainder law: the census family's `e = 3` member closes -/

section Law

/-- ★★★ **`ConeRemainderLaw 3 σ` for EVERY `σ`** — the census family's forced `e = 3`
member (CN5's reduction consumes the family at every `e ≥ 3`): the pair `(X − 1, X^5)`
at the mixed type `{(1,1),(2,1)}`, the pair `(0, 1)` at every other type. -/
theorem coneRemainderLaw_three (σ : FactorizationType) : ConeRemainderLaw 3 σ := by
  by_cases hσ : σ = mixedType
  · subst hσ
    refine (ZcURLim_qmonomial 5).congr ?_
    intro O _ _ _ _ _ π hπ M
    show (((residueCard O : ℕ) : ℝ) - 1) / ((residueCard O : ℕ) : ℝ) ^ 5
      = (coneRemainderCount O 3 mixedType M : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 3))
    rw [coneRemainderCount_three_mixed M]
    have hq2 : 2 ≤ residueCard O := two_le_residueCard O
    have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast [Nat.cast_sub (by omega : 1 ≤ residueCard O)]
    rw [show 3 * (M + 3) = (3 * (M + 3) - 5) + 5 from by omega, pow_add]
    have hA : ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 3) - 5) ≠ 0 := pow_ne_zero _ hqR
    have hw : ((residueCard O : ℕ) : ℝ) ^ 5 ≠ 0 := pow_ne_zero _ hqR
    field_simp
    rw [show 3 * (M + 3) - 5 + 5 - 5 = 3 * (M + 3) - 5 from by omega]
  · refine ZcURLim_zero.congr ?_
    intro O _ _ _ _ _ π hπ M
    show (0 : ℝ) = (coneRemainderCount O 3 σ M : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (3 * (M + 3))
    rw [coneRemainderCount_three_ne hσ M]
    simp

/-- ★★ The `m = 3` zero-cone clause, fired unconditionally (modulo the signed B.42 cite
in the footprint). -/
theorem zeroConeClause_three (σ : FactorizationType) : ZeroConeClause 3 σ :=
  zeroConeClause_of_remainderLaw (by norm_num) σ (coneRemainderLaw_three σ)

end Law

/-! ## §8 — ★★★ the census front, re-based: the `e = 2, 3` members consumed -/

section Front

open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG25 (UnramifiedBlockBridge coneRemainderLaw_two
  decidedSliceAt_all_of_remainder_bridge)

/-- ★★★ **THE CENSUS FRONT, re-based through this file**: with the remainder family
closed at `e = 2` (CN5's `coneRemainderLaw_two`) and `e = 3` (this file's
`coneRemainderLaw_three`), the all-degree decided slice rests on EXACTLY the remainder
laws at `e ≥ 4` and the unramified block bridges (`δ, e ≥ 2`). -/
theorem decidedSliceAt_all_of_remainder4_bridge
    (hR : ∀ e : ℕ, 4 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ → ConeRemainderLaw e σ)
    (hBr : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n := by
  refine decidedSliceAt_all_of_remainder_bridge ?_ hBr
  intro e he hsm σ hσ hwit
  rcases Nat.lt_or_ge e 4 with h4 | h4
  · rcases Nat.lt_or_ge e 3 with h3 | h3
    · have he2 : e = 2 := by omega
      subst he2
      exact coneRemainderLaw_two σ
    · have he3 : e = 3 := by omega
      subst he3
      exact coneRemainderLaw_three σ
  · exact hR e h4 hsm σ hσ hwit

end Front

end Uniformity.Density.IFCG26

end

/-! ## AXCHECK FOOTER — §0/§1 expect Lean core `{propext, Classical.choice, Quot.sound}`;
§§2–7 expect Lean core PLUS exactly the signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42).  The C.33 cites must NOT
occur. -/

#print axioms Uniformity.Density.IFCG26.mem_sideSet_of_onSide
#print axioms Uniformity.Density.IFCG26.le_suppVal_monicPoly
#print axioms Uniformity.Density.IFCG26.onSide_monicPoly_of_npAttains
#print axioms Uniformity.Density.IFCG26.exists_pure_factor_of_two_point_side
#print axioms Uniformity.Density.IFCG26.fracFaceForcesRam_of_stratum
#print axioms Uniformity.Density.IFCG26.dvd_natDegree_of_isPure
#print axioms Uniformity.Density.IFCG26.irreducible_of_isPure_natDegree_eq
#print axioms Uniformity.Density.IFCG26.decidedAt_cubic_mixed
#print axioms Uniformity.Density.IFCG26.remainder_carrier_three
#print axioms Uniformity.Density.IFCG26.card_mixedBox
#print axioms Uniformity.Density.IFCG26.coneRemainderCount_three_mixed
#print axioms Uniformity.Density.IFCG26.coneRemainderCount_three_ne
#print axioms Uniformity.Density.IFCG26.coneRemainderLaw_three
#print axioms Uniformity.Density.IFCG26.zeroConeClause_three
#print axioms Uniformity.Density.IFCG26.decidedSliceAt_all_of_remainder4_bridge
