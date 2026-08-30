/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG22
import Uniformity.ChapB.B15
import Uniformity.ChapB.B18
import Uniformity.ChapB.B35b
import Uniformity.ChapB.B54
import Uniformity.ChapB.B56
import Uniformity.ChapB.B57
import Uniformity.Density.TypePositivity

/-!
# Uniformity.ChapI.IFCG23 — [CN2 2026-08-30] the class-level fractional-face decidedness
criterion at the frame floor

Stage CN2 of the cone census — the blueprint's designated heart
(`runs/wave-c/verdict_ECONE.md` §BLUEPRINT; design record and obstruction resolution in
`runs/wave-c/verdict_CN2.md`).  CN1 (`IFCG22`) made the class Newton polygon lift-stable
STRICTLY below the frame floor (`NPVisibleAt`, support `< e'·N`) and proved that boundary
sharp for polygon data.  This file proves the boundary is where DECIDEDNESS lives:

* **§1–§2 the two bridges.**  `classCoeffVal_exact` (CN1) pins the true `addVal` of every
  lift's coefficient below the window (`npHgt_monicPoly_eq`, via B.15's `npHgt_X`); a class
  face of slope `h/e'` attained at BOTH endpoints `0` and `m` therefore makes EVERY lift
  x-pure in ChapB's sense — ★ `isPure_monicPoly_of_face : IsPure X (monicPoly a) h e'`.
* **§3 the frame-free `e'`-leg.**  `dvd_ramIndexOf_of_isPure` — C61's CLOSED `e₁`-leg
  (`e1_dvd_ramIndexOf_of_mem_monicFactors`, the B.18/B.57/B.35b/B.54 supply) restated with
  the `KeyFrame` fields as plain coprime data `(h, e')`; no frame object is constructed.
* **§4 ★★ THE CRITERION.**  `ramIndexOf_dvd_of_visible_face`: a visible endpoint-attained
  class face of slope `h/e'` (`gcd(h,e') = 1`) forces `e' ∣ ramIndexOf g'` on every monic
  irreducible factor of EVERY lift — the class-level C61 `ℓ`-half at the x-frame, pure case.
  `decidedAt_of_eisenstein_face` (`e' = m`): the face DECIDES the class,
  `DecidedAt O m ⟨{(m,1)}⟩ N c` — uniform in `(q, m, h, N)`.
* **§5 the e = 2 instrument.**  `decidedAt_quad_ram` (depth-`j` ramified cone classes:
  `v₀ = 2j+1 < N`, `v₁ ≥ j+1`), `decidedAt_of_stratum_vzero_one` (the depth-0 cone slice is
  FULLY decided — the `(q−1)q^(2N−3)` monomial's set), and ★ `quad_stratum_reduction`: the
  level-`N` quadratic stratum = (criterion-decided) ∪ (deep `v₀ ≥ 2`, the recentring
  territory) ∪ (trivial window) — the at-floor cone count reduced to CN4's geometric sums
  plus IFCG20's recentred copy.
* **§6 the floor is sharp for DECIDEDNESS.**  ⚠ `not_decidedAt_zero_class`: the zero class
  is `σ`-undecided for EVERY `σ`, every `m ≥ 2`, every window `N` — lifts `X^m`
  (`typeOf_X_pow`: `m × (1,1)`) vs the Eisenstein witness
  (`typeOf_eisenstein_witness`: `{(m,1)}`, decided by the criterion itself at window
  `v+1`).  ⚠ `eisenstein_face_floor_sharp`: at `m = 2`, odd `N`, the zero class carries the
  criterion's FULL hypothesis vector except strict visibility (support `= e'·N` exactly, AT
  the floor) and is undecided — `NPVisibleAt` cannot be relaxed to `≤`.
* **§7 the exact named remainder.**  `FracFaceForcesRamStatement` — the general-position
  face (C61's OPEN `ℓ`-half shape at class level), needing the NP face factorization over a
  complete DVR (Hensel/C133mh-grade input); its pure instance is PROVED
  (`fracFaceForcesRam_pure`).  Also open (prose, verdict §REMAINDER): the residual-polynomial
  refinement at pure faces with `e' < m`, where C.33/C133mh genuinely enter.

## The resolution of the CN1-floor tension (recorded before proving, per charge)

`DecidedAt` quantifies over ALL lifts, so decidedness is a class property BY DEFINITION —
the floor threatens only polygon-based CRITERIA, which may consume only the lift-stable
(strictly visible) data.  Below the floor the visible face decides (§4); at the floor the
criterion's conclusion genuinely FAILS (§6), so CN1's instability is real undecidedness.
CN1's sharp pair `(π,π)`/`(π³,π³)` both happen to be `{(2,1)}` — undecidedness of the floor
class is witnessed by OTHER lifts (`X²`).

## Axiom fence

Lean core everywhere (`propext`, `Classical.choice`, `Quot.sound`); the C.33 cite does not
occur; zero sorries.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG23

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22

attribute [local instance] Classical.propDecidable

/-! ## §1 — the valuation bridge: class-exact valuations pin `addVal` of every lift -/

section ValBridge

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- Exact divisibility pins the additive valuation. -/
theorem addVal_eq_of_pow_dvd_not_dvd {π : O} (hπ : Irreducible π) {v : ℕ} {x : O}
    (hd : π ^ v ∣ x) (hnd : ¬ π ^ (v + 1) ∣ x) :
    IsDiscreteValuationRing.addVal O x = (v : ℕ∞) := by
  have h1 : (v : ℕ∞) ≤ IsDiscreteValuationRing.addVal O x :=
    (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hd
  refine le_antisymm ?_ h1
  by_contra hlt
  rw [not_le] at hlt
  refine hnd ((Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 ?_)
  rw [Nat.cast_add, Nat.cast_one]
  exact Order.add_one_le_of_lt hlt

/-- `π^(v+1)` does not divide `π^v`. -/
theorem not_pow_succ_dvd {π : O} (hπ : Irreducible π) (v : ℕ) : ¬ π ^ (v + 1) ∣ π ^ v := by
  intro hd
  have h1 := (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hd
  rw [hπ.addVal_pow] at h1
  have h2 : v + 1 ≤ v := by exact_mod_cast h1
  omega

end ValBridge

/-! ## §2 — the purity bridge: a visible endpoint-attained class face makes every lift x-pure -/

section PurityBridge

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- Any lift's true x-polygon height dominates the class height (windowed valuation), at
every abscissa below the degree. -/
theorem le_npHgt_monicPoly {π : O} (hπ : Irreducible π) {m N : ℕ} {c : Coeff O m N}
    {a : Fin m → O} (ha : proj O m N a = c) {j : ℕ} (hj : j < m) :
    ((classCoeffVal c ⟨j, hj⟩ : ℕ) : ℕ∞) ≤ npHgt X (monicPoly a) j := by
  rw [npHgt_X, monicPoly_coeff_lt a hj]
  refine (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 ?_
  exact (le_classCoeffVal_iff_dvd hπ (classCoeffVal_le c ⟨j, hj⟩) ha ⟨j, hj⟩).1 le_rfl

/-- Below the window, the class height IS the true x-polygon height of every lift. -/
theorem npHgt_monicPoly_eq {π : O} (hπ : Irreducible π) {m N : ℕ} {c : Coeff O m N}
    {a : Fin m → O} (ha : proj O m N a = c) {j : ℕ} (hj : j < m)
    (hvis : classCoeffVal c ⟨j, hj⟩ < N) :
    npHgt X (monicPoly a) j = ((classCoeffVal c ⟨j, hj⟩ : ℕ) : ℕ∞) := by
  rw [npHgt_X, monicPoly_coeff_lt a hj]
  obtain ⟨hdvd, hnd⟩ := classCoeffVal_exact hπ ha hvis
  exact addVal_eq_of_pow_dvd_not_dvd hπ hdvd hnd

/-- The monic point: the x-polygon height of any lift at the degree abscissa is `0`. -/
theorem npHgt_monicPoly_top {m : ℕ} (a : Fin m → O) :
    npHgt X (monicPoly a) m = 0 := by
  rw [npHgt_X]
  have h1 : (monicPoly a).coeff m = 1 := by
    have h2 := (monicPoly_monic a).coeff_natDegree
    rwa [monicPoly_natDegree] at h2
  rw [h1]
  exact IsDiscreteValuationRing.addVal_one

/-- The class support at slope data `(h, e')` equals `h·m` exactly when it is attained at the
monic point. -/
theorem classNPSupport_eq_of_attains_top {O' : Type*} [CommRing O'] [IsDomain O']
    [IsDiscreteValuationRing O'] {m N h e' : ℕ} {c : Coeff O' m N}
    (hmm : NPAttains c h e' m) : classNPSupport c h e' = h * m := by
  have hnpm : npHeight c m = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl m)]
  have h2 := hmm.2
  rw [hnpm, Nat.mul_zero, Nat.zero_add] at h2
  exact h2.symm

/-- **The support transfer**: if the class support at `(h, e')` is attained at the monic
point (equivalently, equals `h·m`), then the TRUE x-polygon support of every lift is exactly
`h·m`. -/
theorem suppVal_monicPoly_of_attains {π : O} (hπ : Irreducible π) {m N h e' : ℕ}
    {c : Coeff O m N} (hmm : NPAttains c h e' m) {a : Fin m → O}
    (ha : proj O m N a = c) :
    suppVal X (monicPoly a) h e' = ((h * m : ℕ) : ℕ∞) := by
  have hsup : classNPSupport c h e' = h * m := classNPSupport_eq_of_attains_top hmm
  rw [suppVal, monicPoly_natDegree]
  refine le_antisymm ?_ ?_
  · refine le_trans (Finset.inf_le (Finset.mem_range.mpr (Nat.lt_succ_self m))) ?_
    rw [npHgt_monicPoly_top, smul_zero, zero_add]
  · refine Finset.le_inf ?_
    intro j hj
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    rcases eq_or_lt_of_le hj with rfl | hjlt
    · rw [npHgt_monicPoly_top, smul_zero, zero_add]
    · have hcls : classNPSupport c h e' ≤ e' * classCoeffVal c ⟨j, hjlt⟩ + h * j := by
        have h3 := classNPSupport_le_apply c h e' (le_of_lt hjlt)
        unfold npHeight at h3
        rwa [dif_pos hjlt] at h3
      have hle : ((h * m : ℕ) : ℕ∞)
          ≤ ((e' * classCoeffVal c ⟨j, hjlt⟩ + h * j : ℕ) : ℕ∞) := by
        rw [← hsup]
        exact_mod_cast hcls
      refine le_trans hle ?_
      have hh := le_npHgt_monicPoly hπ ha hjlt
      calc ((e' * classCoeffVal c ⟨j, hjlt⟩ + h * j : ℕ) : ℕ∞)
          = e' • ((classCoeffVal c ⟨j, hjlt⟩ : ℕ) : ℕ∞) + ((h * j : ℕ) : ℕ∞) := by
            rw [nsmul_eq_mul]
            push_cast
            ring
        _ ≤ e' • npHgt X (monicPoly a) j + ((h * j : ℕ) : ℕ∞) := by
            rw [nsmul_eq_mul, nsmul_eq_mul]
            gcongr

-- `he'` is kept for signature honesty (the guard against the vacuous slope datum `e' = 0`)
-- even though this particular proof happens not to consume it.
set_option linter.unusedVariables false in
/-- ★ **The purity bridge (CN2's glue).** A class face of slope `h/e'` attained at BOTH
endpoints `0` and `m`, strictly below the frame floor, makes EVERY lift x-pure at `(h, e')`
in ChapB's sense: the lift's whole x-polygon is the single side of slope `−h/e'`. -/
theorem isPure_monicPoly_of_face {π : O} (hπ : Irreducible π) {m N h e' : ℕ}
    (hm0 : 0 < m) (he' : 0 < e') {c : Coeff O m N}
    (h0 : NPAttains c h e' 0) (hmm : NPAttains c h e' m) (hvis : NPVisibleAt c h e')
    {a : Fin m → O} (ha : proj O m N a = c) :
    IsPure X (monicPoly a) h e' := by
  have hsup : classNPSupport c h e' = h * m := classNPSupport_eq_of_attains_top hmm
  have hsupp := suppVal_monicPoly_of_attains hπ hmm ha
  -- the abscissa-0 height of the class: `e' * v₀ = h * m`, and it is visible
  have hv0 : e' * classCoeffVal c ⟨0, hm0⟩ = h * m := by
    have h2 := h0.2
    unfold npHeight at h2
    rw [dif_pos hm0] at h2
    rw [hsup] at h2
    omega
  have hv0vis : classCoeffVal c ⟨0, hm0⟩ < N := by
    have hfl : classNPSupport c h e' < e' * N := hvis
    rw [hsup] at hfl
    have h3 : e' * classCoeffVal c ⟨0, hm0⟩ < e' * N := by omega
    exact Nat.lt_of_mul_lt_mul_left h3
  constructor
  · -- `OnSide` at the abscissa `0`
    show e' • npHgt X (monicPoly a) 0 + ((h * 0 : ℕ) : ℕ∞) = suppVal X (monicPoly a) h e'
    rw [hsupp, npHgt_monicPoly_eq hπ ha hm0 hv0vis, nsmul_eq_mul, Nat.mul_zero,
      Nat.cast_zero, add_zero, ← Nat.cast_mul, hv0]
  · -- `OnSide` at the abscissa `deg / deg X = m`
    have hdeg : (monicPoly a).natDegree / (X : Polynomial O).natDegree = m := by
      rw [monicPoly_natDegree, natDegree_X, Nat.div_one]
    rw [hdeg]
    show e' • npHgt X (monicPoly a) m + ((h * m : ℕ) : ℕ∞) = suppVal X (monicPoly a) h e'
    rw [hsupp, npHgt_monicPoly_top, smul_zero, zero_add]

end PurityBridge

/-! ## §3 — the frame-free `e'`-leg (C61 §3b with the `KeyFrame` fields as plain data) -/

section RamLeg

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- **The `e'`-leg, frame-free** (C61's `e1_dvd_ramIndexOf_of_mem_monicFactors` with
`(F.h, F.e₁)` replaced by plain coprime data `(h, e')`): every monic irreducible factor of an
x-pure polynomial has ramification index divisible by the slope denominator. -/
theorem dvd_ramIndexOf_of_isPure {π : O} (hπ : Irreducible π) {h e' : ℕ} (he' : 0 < e')
    (hcop : Nat.Coprime h e') {g : Polynomial O} (hg : g.Monic)
    (hx : IsPure Polynomial.X g h e') {g' : Polynomial O} (hg' : g' ∈ monicFactors g) :
    e' ∣ ramIndexOf g' := by
  classical
  rcases Nat.eq_zero_or_pos h with hh0 | hh
  · have he1 : e' = 1 := by
      have hc := hcop
      rw [hh0, Nat.coprime_zero_left] at hc
      exact hc
    rw [he1]
    exact one_dvd _
  · have hspec := monicFactors_spec hg
    obtain ⟨hg'm, hg'irr⟩ := hspec.1 g' hg'
    have hg'pos : 0 < g'.natDegree := natDegree_pos_of_mem_monicFactors hg hg'
    obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hg'
    have hprod : g = g' * R.prod := by rw [← hspec.2, hR, Multiset.prod_cons]
    have hRm : R.prod.Monic := by
      have h2 := Polynomial.monic_multiset_prod_of_monic R id
        (fun q hq => (hspec.1 q (by rw [hR]; exact Multiset.mem_cons_of_mem hq)).1)
      rwa [Multiset.map_id] at h2
    have hneg : (sideSet (Polynomial.X : Polynomial O) g h e').Nonempty :=
      sideSet_nonempty Polynomial.monic_X (by simp) hg (μ := g.natDegree) (by simp) h e'
    obtain ⟨hne₁, hne₂, hp₁, hp₂, hsum, hres₁⟩ :=
      isPure_of_monic_factor hπ isKey_X hh he' hcop hg hg'm hRm (by simp) hprod hx hneg
    have hdeq : e' * sideDeg (Polynomial.X : Polynomial O) g' h e' hne₁ = g'.natDegree :=
      sideDeg_of_pure Polynomial.monic_X (by simp) hg'm (by simp) he' hcop hp₁ hne₁
    have hdd : 0 < sideDeg (Polynomial.X : Polynomial O) g' h e' hne₁ := by
      rcases Nat.eq_zero_or_pos (sideDeg (Polynomial.X : Polynomial O) g' h e' hne₁) with
        h0 | hpos
      · rw [h0, Nat.mul_zero] at hdeq; omega
      · exact hpos
    have hB54 := inertiaDegOf_dvd_key_mul_resDeg hπ isKey_X hh he' hcop hg'm hg'pos hp₁
      hne₁ hdd hres₁
    rw [Polynomial.natDegree_X, one_mul] at hB54
    obtain ⟨t, ht⟩ := hB54
    have hfpos : 0 < inertiaDegOf g' := inertiaDegOf_pos (normValues_nonempty hg'm hg'pos)
    have hmul : ramIndexOf g' * inertiaDegOf g' = g'.natDegree :=
      ramIndexOf_mul_inertiaDegOf hg'm hg'pos
    refine ⟨t, ?_⟩
    have hkey : ramIndexOf g' * inertiaDegOf g' = (e' * t) * inertiaDegOf g' := by
      rw [hmul, ← hdeq, ht]; ring
    exact Nat.eq_of_mul_eq_mul_right hfpos hkey

end RamLeg

/-! ## §4 — ★★ THE CRITERION: class-level fractional-face decidedness -/

section Criterion

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **CN2, the ramification forcing** (the class-level C61 `ℓ`-half at the x-frame, pure
case): a class face of slope `h/e'` attained at both endpoints, strictly below the frame
floor, forces `e' ∣ ramIndexOf g'` on every monic irreducible factor `g'` of EVERY lift. -/
theorem ramIndexOf_dvd_of_visible_face {m N h e' : ℕ} (hm0 : 0 < m) (he' : 0 < e')
    (hcop : Nat.Coprime h e') {c : Coeff O m N}
    (h0 : NPAttains c h e' 0) (hmm : NPAttains c h e' m) (hvis : NPVisibleAt c h e')
    {a : Fin m → O} (ha : proj O m N a = c)
    {g' : Polynomial O} (hg' : g' ∈ monicFactors (monicPoly a)) :
    e' ∣ ramIndexOf g' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  exact dvd_ramIndexOf_of_isPure hπ he' hcop (monicPoly_monic a)
    (isPure_monicPoly_of_face hπ hm0 he' h0 hmm hvis ha) hg'

/-- ★★ **CN2 — THE DECIDEDNESS CRITERION (the Eisenstein face, `e' = m`).** A class face of
slope `h/m` with `gcd(h, m) = 1`, attained at both endpoints and strictly below the frame
floor, DECIDES the class: every lift is irreducible and totally ramified,
`typeOf = ⟨{(m, 1)}⟩`. Uniform in `(q, m, h, N)`. -/
theorem decidedAt_of_eisenstein_face {m N h : ℕ} (hm0 : 0 < m)
    (hcop : Nat.Coprime h m) {c : Coeff O m N}
    (h0 : NPAttains c h m 0) (hmm : NPAttains c h m m) (hvis : NPVisibleAt c h m) :
    DecidedAt O m ⟨{(m, 1)}⟩ N c := by
  intro a ha
  have hgm : (monicPoly a).Monic := monicPoly_monic a
  have hA : ∀ p ∈ (typeOf (monicPoly a)).data, m ∣ p.1 := by
    intro p hp
    rw [typeOf_data, Multiset.mem_map] at hp
    obtain ⟨g', hg', rfl⟩ := hp
    simpa [efPair] using
      ramIndexOf_dvd_of_visible_face hm0 hm0 hcop h0 hmm hvis ha hg'
  refine factorizationType_eq_of_dvd hm0 one_pos ?_
    (fun p hp => efPair_pos_of_mem hgm hp) hA (fun p _ => one_dvd _)
  rw [typeOf_degree hgm, monicPoly_natDegree, Nat.mul_one]

end Criterion

/-! ## §5 — the e = 2 instrument: the quadratic-ramified cone -/

section Instrument

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **The quadratic-ramified cone at depth `j` is decided** (the e = 2 instrument, exact
class form): `v₀ = 2j+1` visible odd and `v₁ ≥ j+1` force `typeOf = ⟨{(2,1)}⟩` on every
lift. -/
theorem decidedAt_quad_ram {N j : ℕ} {c : Coeff O 2 N}
    (h0 : classCoeffVal c 0 = 2 * j + 1) (h0vis : 2 * j + 1 < N)
    (h1 : j + 1 ≤ classCoeffVal c 1) :
    DecidedAt O 2 ⟨{(2, 1)}⟩ N c := by
  have hnp0 : npHeight c 0 = 2 * j + 1 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (0 : ℕ) < 2)]
    exact h0
  have hnp1 : j + 1 ≤ npHeight c 1 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (1 : ℕ) < 2)]
    exact h1
  have hnp2 : npHeight c 2 = 0 := by
    unfold npHeight
    rw [dif_neg (by norm_num : ¬ (2 : ℕ) < 2)]
  have hsup : classNPSupport c (2 * j + 1) 2 = (2 * j + 1) * 2 := by
    refine le_antisymm ?_ ?_
    · have h2 := classNPSupport_le_apply c (2 * j + 1) 2 (le_refl 2)
      rw [hnp2] at h2
      omega
    · refine le_classNPSupport ?_
      intro i hi
      interval_cases i
      · rw [hnp0]; omega
      · have h3 := hnp1; omega
      · rw [hnp2]; omega
  have h0att : NPAttains c (2 * j + 1) 2 0 := ⟨by omega, by rw [hnp0, hsup]; ring⟩
  have h2att : NPAttains c (2 * j + 1) 2 2 := ⟨le_refl 2, by rw [hnp2, hsup]; ring⟩
  have hvis : NPVisibleAt c (2 * j + 1) 2 := by
    show classNPSupport c (2 * j + 1) 2 < 2 * N
    rw [hsup]
    omega
  have hcop : Nat.Coprime (2 * j + 1) 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm
  exact decidedAt_of_eisenstein_face (by norm_num) hcop h0att h2att hvis

/-- ★ **The depth-0 slice of the quadratic cone is FULLY decided ramified**: every class of
the stratum of `X²` with `v₀ = 1` is `⟨{(2,1)}⟩`-decided (this is the cone-proper slice whose
count is the `j = 0` monomial `(q−1)·q^(2N−3)`). -/
theorem decidedAt_of_stratum_vzero_one {N : ℕ} (hN : 2 ≤ N)
    {c : Coeff O 2 N} (hc : c ∈ levelZeroStratum O 2 N (X ^ 2))
    (h0 : classCoeffVal c 0 = 1) :
    DecidedAt O 2 ⟨{(2, 1)}⟩ N c := by
  have h1 : 1 ≤ classCoeffVal c 1 :=
    one_le_classCoeffVal_of_mem_stratum (by omega) hc 1
  exact decidedAt_quad_ram (j := 0) (by simpa using h0) (by omega) (by simpa using h1)

/-- ★ **The at-floor cone-count reduction at `e = 2`** (charge item 3's reduction, made a
theorem): every class of the level-`N` stratum of `X²` is EITHER already decided ramified by
the criterion's depth-`0` face, OR lies in the deep part `v₀ ≥ 2` (the recentring territory:
IFCG20's loop classes and the deeper faces, CN3/CN4's job), OR the window is trivial
(`N ≤ 1`, where the whole stratum is the floor and `not_decidedAt_zero_class` applies). The
`⟨{(2,1)}⟩`-decided cone count therefore reduces to the per-depth criterion counts (geometric
monomials, CN4) plus the recentred copy. -/
theorem quad_stratum_reduction {N : ℕ} {c : Coeff O 2 N}
    (hc : c ∈ levelZeroStratum O 2 N (X ^ 2)) :
    DecidedAt O 2 ⟨{(2, 1)}⟩ N c ∨ 2 ≤ classCoeffVal c 0 ∨ N ≤ 1 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · exact Or.inr (Or.inr (by omega))
  rcases Nat.lt_or_ge (classCoeffVal c 0) 2 with h0 | h0
  · have h1 : 1 ≤ classCoeffVal c 0 := one_le_classCoeffVal_of_mem_stratum (by omega) hc 0
    exact Or.inl (decidedAt_of_stratum_vzero_one hN hc (by omega))
  · exact Or.inr (Or.inl h0)

end Instrument

/-! ## §6 — the floor: sharpness of the strict visibility for DECIDEDNESS -/

section Floor

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- `monicPoly 0 = X ^ m`. -/
theorem monicPoly_zero (m : ℕ) : monicPoly (fun _ : Fin m => (0 : O)) = X ^ m := by
  unfold monicPoly
  simp

theorem monicFactors_X_pow (m : ℕ) :
    monicFactors ((X : Polynomial O) ^ m) = Multiset.replicate m X := by
  refine monicFactors_eq ⟨?_, ?_⟩
  · intro g hg
    rw [Multiset.eq_of_mem_replicate hg]
    exact ⟨Polynomial.monic_X, Polynomial.prime_X.irreducible⟩
  · rw [Multiset.prod_replicate]

/-- The type of `X^m`: `m` split linear factors. -/
theorem typeOf_X_pow (m : ℕ) :
    typeOf ((X : Polynomial O) ^ m) = ⟨Multiset.replicate m (1, 1)⟩ := by
  have h1 : (typeOf ((X : Polynomial O) ^ m)).data = Multiset.replicate m (1, 1) := by
    rw [typeOf_data, monicFactors_X_pow, Multiset.map_replicate,
      efPair_of_natDegree_one Polynomial.monic_X Polynomial.natDegree_X]
  calc typeOf ((X : Polynomial O) ^ m)
      = ⟨(typeOf ((X : Polynomial O) ^ m)).data⟩ := rfl
    _ = ⟨Multiset.replicate m (1, 1)⟩ := by rw [h1]

/-- **The Eisenstein witness**: for any `v` coprime to `m > 0`, the polynomial
`X^m + π^v` is irreducible totally ramified, `typeOf = ⟨{(m,1)}⟩` — an instance of the
CRITERION applied at the window `v + 1` (where the face `(0,v)–(m,0)` is strictly visible). -/
theorem typeOf_eisenstein_witness {π : O} (hπ : Irreducible π) {m v : ℕ} (hm0 : 0 < m)
    (hcop : Nat.Coprime v m) :
    typeOf (monicPoly (fun i : Fin m => if (i : ℕ) = 0 then π ^ v else 0)) = ⟨{(m, 1)}⟩ := by
  set a' : Fin m → O := fun i => if (i : ℕ) = 0 then π ^ v else 0 with ha'
  set K := v + 1 with hK
  set c' : Coeff O m K := proj O m K a' with hc'
  have hnp0 : npHeight c' 0 = v := by
    unfold npHeight
    rw [dif_pos hm0]
    show resOrd (Ideal.Quotient.mk _ (a' ⟨0, hm0⟩)) = v
    have ha0 : a' ⟨0, hm0⟩ = π ^ v := rfl
    rw [ha0]
    exact resOrd_mk_eq hπ (Nat.le_succ v) dvd_rfl (Or.inr (not_pow_succ_dvd hπ v))
  have hnpj : ∀ j, ∀ hj : j < m, 0 < j → npHeight c' j = K := by
    intro j hj hj0
    unfold npHeight
    rw [dif_pos hj]
    show resOrd (Ideal.Quotient.mk _ (a' ⟨j, hj⟩)) = K
    have haj : a' ⟨j, hj⟩ = 0 := by
      show (if j = 0 then π ^ v else 0) = 0
      exact if_neg (by omega)
    rw [haj, map_zero]
    exact (resOrd_eq_iff _).mpr rfl
  have hnpm : npHeight c' m = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl m)]
  have hsup : classNPSupport c' v m = v * m := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h2 := classNPSupport_le_apply c' v m (le_refl m)
      rwa [hnpm, Nat.mul_zero, Nat.zero_add] at h2
    · intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hnp0, Nat.mul_zero, Nat.add_zero]
        exact le_of_eq (Nat.mul_comm v m)
      · rcases eq_or_lt_of_le hi with rfl | hilt
        · rw [hnpm, Nat.mul_zero, Nat.zero_add]
        · rw [hnpj i hilt hi0, hK]
          calc v * m = m * v := Nat.mul_comm v m
            _ ≤ m * v + (m + v * i) := Nat.le_add_right _ _
            _ = m * (v + 1) + v * i := by ring
  have h0att : NPAttains c' v m 0 := by
    refine ⟨Nat.zero_le m, ?_⟩
    rw [hnp0, hsup, Nat.mul_zero, Nat.add_zero]
    exact Nat.mul_comm m v
  have hmatt : NPAttains c' v m m := by
    refine ⟨le_refl m, ?_⟩
    rw [hnpm, hsup, Nat.mul_zero, Nat.zero_add]
  have hvis : NPVisibleAt c' v m := by
    show classNPSupport c' v m < m * K
    rw [hsup, hK]
    calc v * m = m * v := Nat.mul_comm v m
      _ < m * v + m := Nat.lt_add_of_pos_right hm0
      _ = m * (v + 1) := by ring
  exact decidedAt_of_eisenstein_face hm0 hcop h0att hmatt hvis a' rfl

/-- ⚠ **The deep boundary is NEVER decided** (uniform in `q, m ≥ 2, N`, every `σ`): the zero
class contains the lift `X^m` (type `m × (1,1)`) and an Eisenstein lift
`X^m + π^(mN+1)` (type `{(m,1)}`, decided by the CRITERION itself at a deeper window). -/
theorem not_decidedAt_zero_class {m N : ℕ} (hm : 2 ≤ m) (σ : FactorizationType) :
    ¬ DecidedAt O m σ N (proj O m N (fun _ => 0)) := by
  intro hdec
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm0 : 0 < m := by omega
  -- lift 1: `X^m`, split type `m × (1,1)`
  have h1 : (⟨Multiset.replicate m ((1 : ℕ), (1 : ℕ))⟩ : FactorizationType) = σ := by
    have h2 := hdec (fun _ => 0) rfl
    rwa [monicPoly_zero, typeOf_X_pow] at h2
  -- lift 2: the Eisenstein witness at exponent `v = m·N + 1`, type `{(m,1)}`
  set v := m * N + 1 with hv
  set a' : Fin m → O := fun i => if (i : ℕ) = 0 then π ^ v else 0 with ha'
  have hcop : Nat.Coprime v m := by
    have h2 : Nat.gcd v m ∣ 1 := by
      have hd1 : Nat.gcd v m ∣ m * N := (Nat.gcd_dvd_right v m).mul_right N
      have hd2 : Nat.gcd v m ∣ v := Nat.gcd_dvd_left v m
      have h3 : v - m * N = 1 := by rw [hv]; simp
      calc Nat.gcd v m ∣ v - m * N := Nat.dvd_sub hd2 hd1
        _ = 1 := h3
    exact Nat.dvd_one.mp h2
  have hproj : proj O m N a' = proj O m N (fun _ => 0) := by
    funext i
    show Ideal.Quotient.mk _ (a' i) = Ideal.Quotient.mk _ (0 : O)
    rw [Ideal.Quotient.eq]
    rcases eq_or_ne (i : ℕ) 0 with hi | hi
    · have hai : a' i = π ^ v := by
        show (if (i : ℕ) = 0 then π ^ v else 0) = π ^ v
        exact if_pos hi
      rw [hai, sub_zero]
      refine (mem_maximalIdeal_pow_iff_dvd_of_irr hπ N _).2 (pow_dvd_pow π ?_)
      calc N ≤ m * N := Nat.le_mul_of_pos_left N hm0
        _ ≤ v := by rw [hv]; exact Nat.le_succ _
    · have hai : a' i = 0 := by
        show (if (i : ℕ) = 0 then π ^ v else 0) = 0
        exact if_neg hi
      rw [hai, sub_zero]
      exact Ideal.zero_mem _
  have h4 : (⟨({(m, 1)} : Multiset (ℕ × ℕ))⟩ : FactorizationType) = σ := by
    have h5 := hdec a' hproj
    rw [typeOf_eisenstein_witness hπ hm0 hcop] at h5
    exact h5
  -- collision: the two types differ (`card`: `m ≠ 1`)
  have hcard := congrArg (fun τ : FactorizationType => Multiset.card τ.data)
    (h1.trans h4.symm)
  simp at hcard
  omega

/-- ⚠ **THE FLOOR IS SHARP FOR DECIDEDNESS** (CN2's companion to CN1's
`npSupport_not_stable_at_floor`): at `m = 2` and odd `N`, the zero class carries the FULL
hypothesis vector of the criterion — face attained at `0` and `2`, coprime slope data
`(N, 2)` — except that its support sits AT the floor (`= 2·N = e'·N`, so `NPVisibleAt`
fails), and it is `σ`-undecided for EVERY `σ`. The strict floor in
`decidedAt_of_eisenstein_face` cannot be relaxed to `≤`. -/
theorem eisenstein_face_floor_sharp {N : ℕ} (hN : Odd N) (hN1 : 1 ≤ N) :
    NPAttains (proj O 2 N (fun _ => (0 : O))) N 2 0 ∧
    NPAttains (proj O 2 N (fun _ => (0 : O))) N 2 2 ∧
    Nat.Coprime N 2 ∧
    classNPSupport (proj O 2 N (fun _ => (0 : O))) N 2 = 2 * N ∧
    ¬ NPVisibleAt (proj O 2 N (fun _ => (0 : O))) N 2 ∧
    ∀ σ, ¬ DecidedAt O 2 σ N (proj O 2 N (fun _ => (0 : O))) := by
  have hc0 : ∀ i : Fin 2, classCoeffVal (proj O 2 N (fun _ : Fin 2 => (0 : O))) i = N := by
    intro i
    show resOrd (Ideal.Quotient.mk ((maximalIdeal O) ^ N) (0 : O)) = N
    rw [map_zero]
    exact (resOrd_eq_iff _).mpr rfl
  set c₀ : Coeff O 2 N := proj O 2 N (fun _ => (0 : O)) with hc₀
  have hnp0 : npHeight c₀ 0 = N := by
    unfold npHeight
    rw [dif_pos (by norm_num : (0 : ℕ) < 2)]
    exact hc0 _
  have hnp1 : npHeight c₀ 1 = N := by
    unfold npHeight
    rw [dif_pos (by norm_num : (1 : ℕ) < 2)]
    exact hc0 _
  have hnp2 : npHeight c₀ 2 = 0 := by
    unfold npHeight
    rw [dif_neg (by norm_num : ¬ (2 : ℕ) < 2)]
  have hsup : classNPSupport c₀ N 2 = 2 * N := by
    refine le_antisymm ?_ (le_classNPSupport ?_)
    · have h2 := classNPSupport_le_apply c₀ N 2 (le_refl 2)
      rw [hnp2] at h2
      omega
    · intro i hi
      interval_cases i
      · rw [hnp0]; omega
      · rw [hnp1]; omega
      · rw [hnp2]; omega
  obtain ⟨k, hk⟩ := hN
  refine ⟨⟨by omega, by rw [hnp0, hsup]; ring⟩,
    ⟨le_refl 2, by rw [hnp2, hsup]; ring⟩,
    (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm,
    hsup, ?_, fun σ => not_decidedAt_zero_class (by norm_num) σ⟩
  intro hvv
  have h5 : classNPSupport c₀ N 2 < 2 * N := hvv
  omega

end Floor

/-! ## §7 — the exact named remainder: the GENERAL-face criterion -/

section Remainder

/-- **The general fractional-face forcing statement — OPEN** (C61's open `ℓ`-half at class
level, general face position): a visible class NP face of fractional slope `h/e'`
(`e' ≥ 2`, `gcd(h,e') = 1`) ANYWHERE on the polygon forces at least one monic irreducible
factor with `e' ∣ ramIndexOf` in every lift. The pure instance (face spanning `[0, m]`) is
PROVED below (`fracFaceForcesRam_pure`); the general position needs the Newton-polygon face
factorization over a complete DVR (Hensel/C133mh-grade input) — the named remainder. -/
def FracFaceForcesRamStatement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (ResidueField O)]
    (m N h e' : ℕ), 2 ≤ e' → Nat.Coprime h e' →
    ∀ c : Coeff O m N, ClassNPFace c h e' → NPVisibleAt c h e' →
    ∀ a : Fin m → O, proj O m N a = c →
      ∃ g' ∈ monicFactors (monicPoly a), e' ∣ ramIndexOf g'

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★ **The PURE instance of the general statement, proved**: when the visible face is
attained at both endpoints `0` and `m`, every lift carries a factor with `e' ∣ ramIndexOf`
(indeed EVERY factor qualifies — `ramIndexOf_dvd_of_visible_face`). -/
theorem fracFaceForcesRam_pure {m N h e' : ℕ} (hm0 : 0 < m) (he' : 0 < e')
    (hcop : Nat.Coprime h e') {c : Coeff O m N}
    (h0 : NPAttains c h e' 0) (hmm : NPAttains c h e' m) (hvis : NPVisibleAt c h e')
    {a : Fin m → O} (ha : proj O m N a = c) :
    ∃ g' ∈ monicFactors (monicPoly a), e' ∣ ramIndexOf g' := by
  have hgm : (monicPoly a).Monic := monicPoly_monic a
  obtain ⟨g', hg'⟩ : ∃ g', g' ∈ monicFactors (monicPoly a) := by
    rcases Multiset.empty_or_exists_mem (monicFactors (monicPoly a)) with h2 | h2
    · exfalso
      have hspec := monicFactors_spec hgm
      have h3 : (monicPoly a).natDegree = 0 := by
        rw [← hspec.2, h2, Multiset.prod_zero]
        exact natDegree_one
      rw [monicPoly_natDegree] at h3
      omega
    · exact h2
  exact ⟨g', hg', ramIndexOf_dvd_of_visible_face hm0 he' hcop h0 hmm hvis ha hg'⟩

end Remainder

end Uniformity.Density.IFCG23

end

/-! ## AXCHECK FOOTER — expect Lean core `{propext, Classical.choice, Quot.sound}`
everywhere; the C.33 cite must NOT occur. -/

#print axioms Uniformity.Density.IFCG23.addVal_eq_of_pow_dvd_not_dvd
#print axioms Uniformity.Density.IFCG23.npHgt_monicPoly_eq
#print axioms Uniformity.Density.IFCG23.suppVal_monicPoly_of_attains
#print axioms Uniformity.Density.IFCG23.isPure_monicPoly_of_face
#print axioms Uniformity.Density.IFCG23.dvd_ramIndexOf_of_isPure
#print axioms Uniformity.Density.IFCG23.ramIndexOf_dvd_of_visible_face
#print axioms Uniformity.Density.IFCG23.decidedAt_of_eisenstein_face
#print axioms Uniformity.Density.IFCG23.decidedAt_quad_ram
#print axioms Uniformity.Density.IFCG23.decidedAt_of_stratum_vzero_one
#print axioms Uniformity.Density.IFCG23.quad_stratum_reduction
#print axioms Uniformity.Density.IFCG23.typeOf_X_pow
#print axioms Uniformity.Density.IFCG23.typeOf_eisenstein_witness
#print axioms Uniformity.Density.IFCG23.not_decidedAt_zero_class
#print axioms Uniformity.Density.IFCG23.eisenstein_face_floor_sharp
#print axioms Uniformity.Density.IFCG23.fracFaceForcesRam_pure
