/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG34
import Uniformity.ChapI.IFCG19
import Uniformity.ChapI.IFC7

/-!
# IFCG36 — the digit-count instrument and the two depth-0 box limits (UNIT DBL)

IFCG34 (ER4) reduced the five even-ramification `e = 4` laws to named sector-limit
premises; two of the survivors are DEPTH-0 BOX LIMITS with closed-form targets:
`ZcURLim e1SplitFam` and `ZcURLim e1IrrFam`.  This module builds the missing
instrument — per-coordinate DIGIT counting on the truncated classes — and closes both.

## The instrument (§1)

`resDig π v x` : the `v`-th `π`-digit of a truncated class `x : Res O K` (B.21's scalar
digit `digAt` read on the canonical representative `resOut x`).  For `v < K` it is class
data (`resDig_mk`), it refines the windowed valuation
(`resOrd x = v ↔ v ≤ resOrd x ∧ resDig π v x ≠ 0`, `resOrd_eq_iff_resDig`), and its
level sets count exactly (`card_setOf_resDig` : `q^(K−v−1)` classes per digit value).

## The E1 residual read as digits (§2)

On the `E1` cell (`v₀ = 2` exact, `v₁ ≥ 2, v₂, v₃ ≥ 1`) EVERY lift's slope-`1/2`
residual quadratic is `Y² + δ₁(c₂)·Y + δ₂(c₀)` — the coefficients are the two class
digits, embedded into `resField X` along the canonical ring iso
`resFieldEquivX : ResidueField O ≃+* resField X` (§3).  This is `e1_resPoly_eq`,
via B.35c's pure-face coefficient formula + B.15's `dev_X` + B.24's digit reading.

## The fibers and the counts (§4)

`e1Fiber π K β α` (both digits pinned) is a product box of card `q^(4K−8)`
(`card_e1Fiber`).  The genre boxes are the fiber unions over the field-side genre sets
of monic quadratics `Y² + βY + α`:

* `card_e1IrrBox_necklace` : `#e1IrrBox = N₂(q) · q^(4K−8)` (`N₂` = IFCG19's necklace
  count of monic irreducible quadratics; `card_irrPairs` is the pair form);
* `card_e1DdBox` : `#e1DdBox = (q−1) · q^(4K−8)` (double roots `Y = r`, `r ≠ 0`);
* `card_e1Box_partition` + closed doubled forms:
  `2·#e1SplitBox = (q−1)(q−2)·q^(4K−8)`, `2·#e1IrrBox = (q²−q)·q^(4K−8)`.

## The limits and the rewired laws (§5–§6)

* ★★ `zcURLim_e1SplitFam` : the split-sector depth-0 limit — value `(q−1)(q−2)/(2q⁸)`.
* ★★ `zcURLim_e1IrrFam` : the irreducible-sector depth-0 limit — value `N₂(q)/q⁸`.
* The `∀ σ` decided-sector families discharge: `zcURLim_e1SplitDecFam` (UNCONDITIONAL —
  the split box is `{(2,1),(2,1)}`-decided, all other σ get the empty set) and
  `zcURLim_e1IrrDecFam` (under the named leaf `E1IrrLeafDecision`).
* ★★ the rewired laws: `coneRemainderLaw_four_ramPair` now needs ONLY the two recursion
  terms (dd + E2); `coneRemainderLaw_four_type22` needs ONLY the leaf + dd.
* ★★★ `decidedSliceAt_all_of_recursion_limits` : the census front with the two depth-0
  box limits CLOSED — the surviving open set is exactly the leaf, the `∀ σ` dd/E2
  recursion families, the `e ≥ 5` laws, and the block bridges.

Axiom expectation: §§1–4 Lean core; the resPoly-consuming and law sections Lean core
plus exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42), inherited through IFCG34.
-/

noncomputable section

namespace Uniformity.Density.IFCG36

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFC7 (resOut mk_resOut)
open Uniformity.Density.IFCG22 (classNPSupport npHeight NPAttains NPVisibleAt
  classNPSupport_le_apply le_classNPSupport)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero card_setOf_le_resOrd
  card_setOf_resOrd_eq card_pi_set coneRemainderCount ConeRemainderLaw)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains)
open Uniformity.Density.IFCG19 (necklacePoly necklacePoly_eval_card)
open Uniformity.Density.IFCG31 (ramPairType)
open Uniformity.Density.IFCG34 (e1Box mem_e1Box_iff card_e1Box e1SplitBox e1IrrBox
  e1DdBox e1Box_eq_genres disjoint_e1SplitBox_e1IrrBox disjoint_e1SplitBox_e1DdBox
  disjoint_e1IrrBox_e1DdBox type22 type41 E1IrrLeafDecision e1SplitFam e1IrrFam
  e1SplitDecFam e1IrrDecFam e1DdDecFam e2DecFam decided_inter_e1Split_eq_self
  decided_inter_e1Split_eq_empty decided_inter_e1Irr_eq_empty
  decided_inter_e1Irr_of_leaf decided41_inter_e1Irr_of_leaf
  coneRemainderLaw_four_ramPair_of_sectors coneRemainderLaw_four_type22_of_sectors
  decidedSliceAt_all_of_sector_limits)

attribute [local instance] Classical.propDecidable

/-! ## §1 — the digit-count instrument on truncated classes -/

section Digits

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] {π : O}

/-- **The class digit.** `resDig π v x` : the `v`-th `π`-digit of the truncated class
`x : Res O K`, read on the canonical representative (junk `0` when the valuation is too
small).  For `v < K` this is class data (`resDig_mk`). -/
def resDig (π : O) (v : ℕ) {K : ℕ} (x : Res O K) : ResidueField O :=
  digAt π v (resOut x)

omit [Finite (ResidueField O)] in
/-- The digit congruence (IFCG28's private `digAt_congr`, reproduced): digits strictly
below the window are stable under level-`N` perturbation. -/
private theorem digAt_congr (hπ : Irreducible π) {N k : ℕ} (hk : k < N)
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

/-- **The digit is class data**: on any representative, `resDig` of the class is the
digit of the representative (strictly below the window). -/
theorem resDig_mk (hπ : Irreducible π) {K v : ℕ} (hv : v < K) (x : O) :
    resDig π v (Ideal.Quotient.mk ((maximalIdeal O) ^ K) x) = digAt π v x := by
  show digAt π v (resOut (Ideal.Quotient.mk ((maximalIdeal O) ^ K) x)) = digAt π v x
  refine digAt_congr hπ hv ?_
  have h1 : Ideal.Quotient.mk ((maximalIdeal O) ^ K)
      (resOut (Ideal.Quotient.mk ((maximalIdeal O) ^ K) x))
      = Ideal.Quotient.mk ((maximalIdeal O) ^ K) x := mk_resOut _
  exact (mem_maximalIdeal_pow_iff_dvd_of_irr hπ K _).1 (Ideal.Quotient.eq.mp h1)

/-- **The digit level-set count**: `q^(K−v−1)` classes carry a given digit at a given
admissible height. -/
theorem card_setOf_resDig (hπ : Irreducible π) {K v : ℕ} (hv : v < K)
    (d : ResidueField O) :
    Nat.card ({x : Res O K | v ≤ resOrd x ∧ resDig π v x = d} : Set (Res O K))
      = residueCard O ^ (K - (v + 1)) := by
  classical
  obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective (R := O) d
  have hπ0 : residue O π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).2
      ((mem_maximalIdeal_iff_dvd hπ π).2 dvd_rfl)
  have hset : ({x : Res O K | v ≤ resOrd x ∧ resDig π v x = d} : Set (Res O K))
      = (fun y => Ideal.Quotient.mk ((maximalIdeal O) ^ K) (π ^ v * s) + y) ''
        {y : Res O K | v + 1 ≤ resOrd y} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hord, hdig⟩
      have hxout : Ideal.Quotient.mk ((maximalIdeal O) ^ K) (resOut x) = x := mk_resOut x
      have hdvd : π ^ v ∣ resOut x := by
        rw [← resOrd_ge_iff hπ hv.le (resOut x), hxout]
        exact hord
      obtain ⟨w, hw⟩ := hdvd
      have hwd : residue O w = d := by
        rw [← hdig]
        exact (digAt_eq hπ hw).symm
      have hres : residue O (w - s) = 0 := by rw [map_sub, hwd, hs, sub_self]
      obtain ⟨t, ht⟩ := (mem_maximalIdeal_iff_dvd hπ _).1
        ((IsLocalRing.residue_eq_zero_iff _).1 hres)
      refine ⟨Ideal.Quotient.mk _ (π ^ v * (w - s)), ?_, ?_⟩
      · rw [resOrd_ge_iff hπ (by omega) _, ht]
        exact ⟨t, by ring⟩
      · rw [← map_add, ← hxout, hw]
        congr 1
        ring
    · rintro ⟨y, hy, rfl⟩
      have hyout : Ideal.Quotient.mk ((maximalIdeal O) ^ K) (resOut y) = y := mk_resOut y
      have hdvd : π ^ (v + 1) ∣ resOut y := by
        rw [← resOrd_ge_iff hπ (by omega : v + 1 ≤ K) (resOut y), hyout]
        exact hy
      obtain ⟨t, ht⟩ := hdvd
      have hsum : Ideal.Quotient.mk ((maximalIdeal O) ^ K) (π ^ v * s) + y
          = Ideal.Quotient.mk ((maximalIdeal O) ^ K) (π ^ v * (s + π * t)) := by
        rw [← hyout, ← map_add, ht]
        congr 1
        ring
      constructor
      · rw [hsum, resOrd_ge_iff hπ hv.le]
        exact ⟨s + π * t, rfl⟩
      · rw [hsum, resDig_mk hπ hv, digAt_eq hπ rfl, map_add, hs, map_mul, hπ0,
          zero_mul, add_zero]
  rw [hset, Nat.card_image_of_injective (add_right_injective _),
    card_setOf_le_resOrd (show v + 1 ≤ K by omega)]

/-- **The digit refines the windowed valuation**: exactness at `v` is reachability plus
a nonzero digit. -/
theorem resOrd_eq_iff_resDig (hπ : Irreducible π) {K v : ℕ} (hv : v < K)
    (x : Res O K) : resOrd x = v ↔ v ≤ resOrd x ∧ resDig π v x ≠ 0 := by
  have hxout : Ideal.Quotient.mk ((maximalIdeal O) ^ K) (resOut x) = x := mk_resOut x
  constructor
  · intro h
    refine ⟨le_of_eq h.symm, ?_⟩
    have hdvd : π ^ v ∣ resOut x := by
      rw [← resOrd_ge_iff hπ hv.le (resOut x), hxout]
      omega
    intro h0
    have h1 : π ^ (v + 1) ∣ resOut x := (digAt_eq_zero_iff hπ hdvd).1 h0
    have h2 : v + 1 ≤ resOrd x := by
      rw [← hxout]
      exact (resOrd_ge_iff hπ (by omega) _).2 h1
    omega
  · rintro ⟨hle, hne⟩
    by_contra hne'
    have h2 : v + 1 ≤ resOrd x := by omega
    have h1 : π ^ (v + 1) ∣ resOut x := by
      rw [← resOrd_ge_iff hπ (by omega : v + 1 ≤ K) (resOut x), hxout]
      exact h2
    have hdvd : π ^ v ∣ resOut x := (pow_dvd_pow π (by omega)).trans h1
    exact hne ((digAt_eq_zero_iff hπ hdvd).2 h1)

end Digits

/-! ## §2 — the coefficient iso `ResidueField O ≃+* resField X` and genre transport -/

section Iso

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- The canonical coefficient embedding into the x-frame residual field. -/
def resIota (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ResidueField O →+* resField (X : Polynomial O) :=
  AdjoinRoot.of ((X : Polynomial O).map (IsLocalRing.residue O))

/-- `resMk` of a constant is the embedded scalar digit. -/
private theorem resMk_C {π : O} (hπ : Irreducible π) (k : ℕ) (t : O) :
    resMk π (X : Polynomial O) k (Polynomial.C t) = resIota O (digAt π k t) := by
  have h : digPoly π k (Polynomial.C t) = Polynomial.C (digAt π k t) := by
    refine Polynomial.ext fun i => ?_
    rw [digPoly_coeff hπ]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [Polynomial.coeff_C_zero, Polynomial.coeff_C_zero]
    · rw [Polynomial.coeff_C, Polynomial.coeff_C, if_neg (by omega), if_neg (by omega)]
      exact (digAt_eq hπ (mul_zero (π ^ k)).symm).trans (map_zero _)
  rw [resMk, h, AdjoinRoot.mk_C]
  rfl

/-- The embedding is bijective: the x-frame residual field IS the residue field. -/
theorem resIota_bijective : Function.Bijective (resIota O) := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  constructor
  · exact RingHom.injective (resIota O)
  · intro z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    refine ⟨p.coeff 0, ?_⟩
    have hroot : AdjoinRoot.root ((X : Polynomial O).map (IsLocalRing.residue O)) = 0 := by
      have h := AdjoinRoot.eval₂_root ((X : Polynomial O).map (IsLocalRing.residue O))
      rwa [Polynomial.eval₂_map, Polynomial.eval₂_X] at h
    have hmk : AdjoinRoot.mk ((X : Polynomial O).map (IsLocalRing.residue O)) p
        = Polynomial.eval₂ (AdjoinRoot.of _) (AdjoinRoot.root _) p := by
      rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
    rw [hmk, hroot, Polynomial.eval₂_at_zero]
    rfl

/-- The canonical ring iso `ResidueField O ≃+* resField X`. -/
def resFieldEquivX : ResidueField O ≃+* resField (X : Polynomial O) :=
  RingEquiv.ofBijective (resIota O) resIota_bijective

theorem resFieldEquivX_apply (t : ResidueField O) :
    resFieldEquivX (O := O) t = resIota O t := rfl

theorem resFieldEquivX_symm_iota (t : ResidueField O) :
    (resFieldEquivX (O := O)).symm (resIota O t) = t := by
  rw [← resFieldEquivX_apply]
  exact RingEquiv.symm_apply_apply _ _

/-- The embedded quadratic is the mapped quadratic. -/
private theorem iota_quad_eq_map (b a : ResidueField O) :
    (X ^ 2 + Polynomial.C (resIota O b) * X + Polynomial.C (resIota O a)
        : Polynomial (resField (X : Polynomial O)))
      = Polynomial.mapEquiv (resFieldEquivX (O := O))
          (X ^ 2 + Polynomial.C b * X + Polynomial.C a) := by
  rw [Polynomial.mapEquiv_apply]
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C]
  rfl

/-- Irreducibility of the embedded quadratic descends to the residue field. -/
theorem irreducible_iota_quad_iff (b a : ResidueField O) :
    Irreducible (X ^ 2 + Polynomial.C (resIota O b) * X + Polynomial.C (resIota O a))
      ↔ Irreducible (X ^ 2 + Polynomial.C b * X + Polynomial.C a) := by
  rw [iota_quad_eq_map]
  exact MulEquiv.irreducible_iff (Polynomial.mapEquiv (resFieldEquivX (O := O)))

/-- The monic-linear-square genre descends to the residue field. -/
theorem sq_iota_quad_iff (b a : ResidueField O) :
    (∃ L : Polynomial (resField (X : Polynomial O)), L.Monic ∧ L.natDegree = 1 ∧
        X ^ 2 + Polynomial.C (resIota O b) * X + Polynomial.C (resIota O a) = L ^ 2)
      ↔ (∃ L : Polynomial (ResidueField O), L.Monic ∧ L.natDegree = 1 ∧
        X ^ 2 + Polynomial.C b * X + Polynomial.C a = L ^ 2) := by
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  constructor
  · rintro ⟨L, hLm, hLd, hLe⟩
    refine ⟨L.map ((resFieldEquivX (O := O)).symm : resField (X : Polynomial O) →+* ResidueField O),
      hLm.map _, by rw [hLm.natDegree_map]; exact hLd, ?_⟩
    have h := congrArg (Polynomial.map
      ((resFieldEquivX (O := O)).symm : resField (X : Polynomial O) →+* ResidueField O)) hLe
    rw [Polynomial.map_pow] at h
    rw [← h]
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C]
    rw [show ((resFieldEquivX (O := O)).symm : resField (X : Polynomial O) →+* ResidueField O)
        (resIota O b) = b from resFieldEquivX_symm_iota b,
      show ((resFieldEquivX (O := O)).symm : resField (X : Polynomial O) →+* ResidueField O)
        (resIota O a) = a from resFieldEquivX_symm_iota a]
  · rintro ⟨L, hLm, hLd, hLe⟩
    refine ⟨L.map ((resFieldEquivX (O := O)) : ResidueField O →+* resField (X : Polynomial O)),
      hLm.map _, by rw [hLm.natDegree_map]; exact hLd, ?_⟩
    have h := congrArg (Polynomial.map
      ((resFieldEquivX (O := O)) : ResidueField O →+* resField (X : Polynomial O))) hLe
    rw [Polynomial.map_pow] at h
    rw [← h]
    simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.map_C]
    rfl

end Iso

/-! ## §3 — the E1 lift bank replay and the residual read as digits -/

section Bridge

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The E1 purity replay (IFCG34's private bank, trimmed to the purity leg). -/
private theorem e1_pure {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e1Box O K) {a : Fin 4 → O} (ha : proj O 4 K a = c) :
    IsPure X (monicPoly a) 1 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := (mem_e1Box_iff c).1 hc
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
  have hvis : NPVisibleAt c 1 2 := by
    show classNPSupport c 1 2 < 2 * K
    rw [hsup]
    omega
  obtain ⟨hO0, hsupp⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hAt0 ha
  obtain ⟨hO4, -⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hAt4 ha
  have hdegdiv : (monicPoly a).natDegree / (X : Polynomial O).natDegree = 4 := by
    rw [monicPoly_natDegree, Polynomial.natDegree_X]
  exact ⟨hO0, by rw [hdegdiv]; exact hO4⟩

/-- ★★ **THE BRIDGE — the E1 residual read as class digits**: every lift of an `e1Box`
class reads the residual quadratic `Y² + δ₁(c₂)·Y + δ₂(c₀)` at the `[0,4]` face. -/
theorem e1_resPoly_eq {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e1Box O K) {a : Fin 4 → O} (ha : proj O 4 K a = c) :
    resPoly π X (monicPoly a) 1 2 (sideSet_nonempty_gen X (monicPoly a) 1 2) 2
      = X ^ 2 + Polynomial.C (resIota O (resDig π 1 (c 2))) * X
          + Polynomial.C (resIota O (resDig π 2 (c 0))) := by
  have hgm : (monicPoly a).Monic := monicPoly_monic a
  have hgdeg4 : (monicPoly a).natDegree = 4 * (X : Polynomial O).natDegree := by
    rw [monicPoly_natDegree, Polynomial.natDegree_X, Nat.mul_one]
  have hpure : IsPure X (monicPoly a) 1 2 := e1_pure hK hπ hc ha
  have hd0 : resDig π 2 (c 0) = digAt π 2 (a 0) := by
    rw [← congrFun ha 0]
    exact resDig_mk hπ (by omega) (a 0)
  have hd2 : resDig π 1 (c 2) = digAt π 1 (a 2) := by
    rw [← congrFun ha 2]
    exact resDig_mk hπ (by omega) (a 2)
  rw [hd0, hd2]
  refine Polynomial.ext fun k => ?_
  rw [resPoly_coeff_of_pure hπ Polynomial.monic_X (by simp) hgm hgdeg4
    (by norm_num) (Nat.coprime_one_left 2) hpure (sideSet_nonempty_gen _ _ 1 2) 2 k]
  rcases k with _ | k
  · rw [Nat.sub_zero, dev_X,
      show (monicPoly a).coeff 0 = a 0 from monicPoly_coeff_lt a (by norm_num),
      resMk_C hπ]
    simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_C]
  · rcases k with _ | k
    · rw [show (2 : ℕ) - 1 * 1 = 1 by norm_num, show (2 : ℕ) * 1 = 2 by norm_num, dev_X,
        show (monicPoly a).coeff 2 = a 2 from monicPoly_coeff_lt a (by norm_num),
        resMk_C hπ]
      simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    · rcases k with _ | k
      · rw [show (2 : ℕ) - 1 * 2 = 0 by norm_num, show (2 : ℕ) * 2 = 4 by norm_num,
          dev_top Polynomial.monic_X (by simp) hgm (μ := 4) hgdeg4, resMk_one hπ]
        simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]
      · have hzero : (monicPoly a).coeff (2 * (k + 3)) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [monicPoly_natDegree]
          omega
        rw [dev_X, hzero, Polynomial.C_0, resMk_of_zero hπ]
        simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
          Polynomial.coeff_X, Polynomial.coeff_C, if_neg (by omega : ¬ k + 3 = 2),
          if_neg (by omega : ¬ k + 3 = 0)]
        rw [if_neg (by omega : ¬ (1 : ℕ) = k + 1 + 1 + 1)]
        ring

end Bridge

/-! ## §4 — the field-side genre pair sets and their counts -/

section Pairs

variable {F : Type*} [Field F]

/-- The coefficient pairs of irreducible monic quadratics. -/
def irrPairs (F : Type*) [Field F] : Set (F × F) :=
  {p | Irreducible (X ^ 2 + Polynomial.C p.1 * X + Polynomial.C p.2)}

/-- The coefficient pairs of monic-linear squares with nonzero constant term. -/
def ddPairs (F : Type*) [Field F] : Set (F × F) :=
  {p | p.2 ≠ 0 ∧ ∃ L : Polynomial F, L.Monic ∧ L.natDegree = 1 ∧
    X ^ 2 + Polynomial.C p.1 * X + Polynomial.C p.2 = L ^ 2}

private theorem quad_coeff_one (b a : F) :
    (X ^ 2 + Polynomial.C b * X + Polynomial.C a : Polynomial F).coeff 1 = b := by
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

private theorem quad_coeff_zero (b a : F) :
    (X ^ 2 + Polynomial.C b * X + Polynomial.C a : Polynomial F).coeff 0 = a := by
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C]

private theorem quad_natDegree (b a : F) :
    (X ^ 2 + Polynomial.C b * X + Polynomial.C a : Polynomial F).natDegree = 2 := by
  compute_degree!

private theorem quad_monic (b a : F) :
    (X ^ 2 + Polynomial.C b * X + Polynomial.C a : Polynomial F).Monic := by
  show (X ^ 2 + Polynomial.C b * X + Polynomial.C a : Polynomial F).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, quad_natDegree]
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]

/-- Monic quadratic reconstruction from its two low coefficients. -/
theorem monic_quadratic_eq_coeffs {G : Polynomial F} (hm : G.Monic)
    (hd : G.natDegree = 2) :
    G = X ^ 2 + Polynomial.C (G.coeff 1) * X + Polynomial.C (G.coeff 0) := by
  have hc2 : G.coeff 2 = 1 := by
    have h := hm.coeff_natDegree
    rwa [hd] at h
  refine Polynomial.ext fun k => ?_
  rcases k with _ | _ | _ | k
  · rw [quad_coeff_zero]
  · rw [quad_coeff_one]
  · rw [hc2]
    simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; omega)]
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C, if_neg (by omega : ¬ k + 3 = 2),
      if_neg (by omega : ¬ k + 3 = 0)]
    rw [if_neg (by omega : ¬ (1 : ℕ) = k + 1 + 1 + 1)]
    ring

/-- An irreducible monic quadratic has nonzero constant term. -/
theorem irrPairs_snd_ne_zero {p : F × F} (hp : p ∈ irrPairs F) : p.2 ≠ 0 := by
  intro h0
  have hirr : Irreducible (X ^ 2 + Polynomial.C p.1 * X + Polynomial.C p.2) := hp
  have hfact : (X ^ 2 + Polynomial.C p.1 * X + Polynomial.C p.2 : Polynomial F)
      = X * (X + Polynomial.C p.1) := by
    rw [h0, Polynomial.C_0]
    ring
  rw [hfact] at hirr
  rcases hirr.isUnit_or_isUnit rfl with h | h
  · exact Polynomial.not_isUnit_X h
  · refine Polynomial.not_isUnit_of_natDegree_pos _ ?_ h
    rw [Polynomial.natDegree_X_add_C]
    omega

/-- The pair set of irreducible quadratics is the necklace carrier. -/
theorem card_irrPairs :
    Nat.card (irrPairs F) = Nat.card (IFCG4.IrredOfDeg F 2) := by
  refine Nat.card_congr
    { toFun := fun p =>
        ⟨X ^ 2 + Polynomial.C p.1.1 * X + Polynomial.C p.1.2,
          quad_monic _ _, quad_natDegree _ _, p.2⟩
      invFun := fun G => ⟨(G.1.coeff 1, G.1.coeff 0), by
        show Irreducible _
        rw [← monic_quadratic_eq_coeffs G.2.1 G.2.2.1]
        exact G.2.2.2⟩
      left_inv := fun p =>
        Subtype.ext (Prod.ext (quad_coeff_one _ _) (quad_coeff_zero _ _))
      right_inv := fun G =>
        Subtype.ext (monic_quadratic_eq_coeffs G.2.1 G.2.2.1).symm }

private theorem sq_X_add_C (t : F) :
    ((X + Polynomial.C t : Polynomial F)) ^ 2
      = X ^ 2 + Polynomial.C (t + t) * X + Polynomial.C (t * t) := by
  rw [Polynomial.C_add, Polynomial.C_mul]
  ring

/-- The double-root pair count: `q − 1`. -/
theorem card_ddPairs [Finite F] : Nat.card (ddPairs F) = Nat.card F - 1 := by
  classical
  have hset : ddPairs F = (fun t : F => (t + t, t * t)) '' {t : F | t ≠ 0} := by
    ext p
    simp only [ddPairs, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hne, L, hLm, hLd, hLe⟩
      rw [hLm.eq_X_add_C hLd, sq_X_add_C] at hLe
      have h1 : p.1 = L.coeff 0 + L.coeff 0 := by
        have h := congrArg (fun q => Polynomial.coeff q 1) hLe
        simpa [quad_coeff_one] using h
      have h0 : p.2 = L.coeff 0 * L.coeff 0 := by
        have h := congrArg (fun q => Polynomial.coeff q 0) hLe
        simpa [quad_coeff_zero] using h
      refine ⟨L.coeff 0, ?_, ?_⟩
      · intro ht0
        exact hne (by rw [h0, ht0, mul_zero])
      · show (L.coeff 0 + L.coeff 0, L.coeff 0 * L.coeff 0) = p
        exact Prod.ext h1.symm h0.symm
    · rintro ⟨t, ht0, rfl⟩
      exact ⟨mul_ne_zero ht0 ht0, X + Polynomial.C t, Polynomial.monic_X_add_C t,
        Polynomial.natDegree_X_add_C t, (sq_X_add_C t).symm⟩
  have hinj : Function.Injective (fun t : F => (t + t, t * t)) := by
    intro t s h
    have h1 : t + t = s + s := congrArg Prod.fst h
    have h2 : t * t = s * s := congrArg Prod.snd h
    have hsq : (t - s) ^ 2 = 0 := by linear_combination h2 - s * h1
    have := pow_eq_zero_iff (n := 2) (by omega) |>.1 hsq
    exact sub_eq_zero.1 this
  have hne : ({t : F | t ≠ 0} : Set F) = Set.univ \ {0} := by
    ext t
    simp
  rw [hset, Nat.card_image_of_injective hinj, hne, Nat.card_coe_set_eq,
    Set.ncard_sdiff (by simp : ({0} : Set F) ⊆ Set.univ), Set.ncard_univ,
    Set.ncard_singleton]

end Pairs

section NecklaceTwo

/-- The degree-2 necklace polynomial, evaluated: `2·N₂(x) = x² − x`. -/
theorem necklacePoly_two_eval (x : ℚ) : (necklacePoly 2).eval x * 2 = x ^ 2 - x := by
  rw [necklacePoly, show Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, ArithmeticFunction.moebius_apply_one]
  rw [show ArithmeticFunction.moebius 2 = -1 from
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  push_cast
  ring

/-- The monic irreducible quadratic count, closed: `2·N₂ = q² − q`. -/
theorem two_mul_card_irredOfDeg_two (F : Type*) [Field F] [Fintype F] :
    2 * Nat.card (IFCG4.IrredOfDeg F 2) = Fintype.card F ^ 2 - Fintype.card F := by
  have h2 := necklacePoly_two_eval ((Fintype.card F : ℚ))
  rw [necklacePoly_eval_card F 2 (by norm_num)] at h2
  have hle : Fintype.card F ≤ Fintype.card F ^ 2 := Nat.le_self_pow (by norm_num) _
  have hcast : ((2 * Nat.card (IFCG4.IrredOfDeg F 2) : ℕ) : ℚ)
      = ((Fintype.card F ^ 2 - Fintype.card F : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hle]
    linarith
  exact_mod_cast hcast

end NecklaceTwo

/-! ## §5 — the fiber boxes and the three genre counts -/

section Fibers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The digit fiber box**: the E1 cell with both residual digits pinned. -/
def e1Fiber (π : O) (K : ℕ) (β α : ResidueField O) : Set (Coeff O 4 K) :=
  {c | ∀ i : Fin 4,
    c i ∈ (if (i : ℕ) = 0 then {x : Res O K | 2 ≤ resOrd x ∧ resDig π 2 x = α}
      else if (i : ℕ) = 1 then {x : Res O K | 2 ≤ resOrd x}
      else if (i : ℕ) = 2 then {x : Res O K | 1 ≤ resOrd x ∧ resDig π 1 x = β}
      else {x : Res O K | 1 ≤ resOrd x})}

omit [Finite (ResidueField O)] in
theorem mem_e1Fiber_iff {π : O} {K : ℕ} {β α : ResidueField O} (c : Coeff O 4 K) :
    c ∈ e1Fiber π K β α ↔ (2 ≤ resOrd (c 0) ∧ resDig π 2 (c 0) = α)
      ∧ 2 ≤ resOrd (c 1) ∧ (1 ≤ resOrd (c 2) ∧ resDig π 1 (c 2) = β)
      ∧ 1 ≤ resOrd (c 3) := by
  constructor
  · intro hc
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    have h3 := hc 3
    rw [if_pos (show ((0 : Fin 4) : ℕ) = 0 from rfl)] at h0
    rw [if_neg (show ¬ ((1 : Fin 4) : ℕ) = 0 by decide),
      if_pos (show ((1 : Fin 4) : ℕ) = 1 from rfl)] at h1
    rw [if_neg (show ¬ ((2 : Fin 4) : ℕ) = 0 by decide),
      if_neg (show ¬ ((2 : Fin 4) : ℕ) = 1 by decide),
      if_pos (show ((2 : Fin 4) : ℕ) = 2 from rfl)] at h2
    rw [if_neg (show ¬ ((3 : Fin 4) : ℕ) = 0 by decide),
      if_neg (show ¬ ((3 : Fin 4) : ℕ) = 1 by decide),
      if_neg (show ¬ ((3 : Fin 4) : ℕ) = 2 by decide)] at h3
    exact ⟨h0, h1, h2, h3⟩
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

/-- ★ **The fiber count**: `q^(4K−8)` classes per digit pair. -/
theorem card_e1Fiber {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    (β α : ResidueField O) :
    Nat.card (e1Fiber π K β α : Set (Coeff O 4 K))
      = residueCard O ^ (4 * K - 8) := by
  classical
  unfold e1Fiber
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
  rw [card_setOf_resDig hπ (show 2 < K by omega) α,
    card_setOf_le_resOrd (show 2 ≤ K by omega),
    card_setOf_resDig hπ (show 1 < K by omega) β,
    card_setOf_le_resOrd (show 1 ≤ K by omega)]
  rw [show K - (2 + 1) = K - 3 from by omega, show K - (1 + 1) = K - 2 from by omega,
    show 4 * K - 8 = (K - 3) + (K - 2) + ((K - 2) + (K - 1)) from by omega,
    pow_add, pow_add]
  ring

/-- E1 membership is fiber membership at the class's own digits (nonzero low digit). -/
theorem mem_e1Box_iff_fiber {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    (c : Coeff O 4 K) :
    c ∈ e1Box O K ↔ resDig π 2 (c 0) ≠ 0
      ∧ c ∈ e1Fiber π K (resDig π 1 (c 2)) (resDig π 2 (c 0)) := by
  rw [mem_e1Box_iff, mem_e1Fiber_iff]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    have hd := (resOrd_eq_iff_resDig hπ (show 2 < K by omega) (c 0)).1 h0
    exact ⟨hd.2, ⟨hd.1, rfl⟩, h1, ⟨h2, rfl⟩, h3⟩
  · rintro ⟨hne, ⟨hA, -⟩, hB, ⟨hC, -⟩, hD⟩
    exact ⟨(resOrd_eq_iff_resDig hπ (show 2 < K by omega) (c 0)).2 ⟨hA, hne⟩, hB, hC, hD⟩

end Fibers

section GenreCounts

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

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

/-- The genre membership as digit-pair membership: irreducible sector. -/
theorem mem_e1IrrBox_iff_pairs {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    (c : Coeff O 4 K) :
    c ∈ e1IrrBox π K ↔ c ∈ e1Box O K
      ∧ (resDig π 1 (c 2), resDig π 2 (c 0)) ∈ irrPairs (ResidueField O) := by
  constructor
  · rintro ⟨hc, a, ha, hirr⟩
    refine ⟨hc, ?_⟩
    rw [e1_resPoly_eq hK hπ hc ha] at hirr
    exact (irreducible_iota_quad_iff _ _).1 hirr
  · rintro ⟨hc, hp⟩
    obtain ⟨a, ha⟩ := proj_surjective O 4 K c
    refine ⟨hc, a, ha, ?_⟩
    rw [e1_resPoly_eq hK hπ hc ha]
    exact (irreducible_iota_quad_iff _ _).2 hp

/-- The genre membership as digit-pair membership: double-root sector. -/
theorem mem_e1DdBox_iff_pairs {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    (c : Coeff O 4 K) :
    c ∈ e1DdBox π K ↔ c ∈ e1Box O K
      ∧ (resDig π 1 (c 2), resDig π 2 (c 0)) ∈ ddPairs (ResidueField O) := by
  constructor
  · rintro ⟨hc, a, ha, L, hLm, hLd, hLe⟩
    refine ⟨hc, ?_, ?_⟩
    · have h0 := ((mem_e1Box_iff c).1 hc).1
      exact ((resOrd_eq_iff_resDig hπ (show 2 < K by omega) (c 0)).1 h0).2
    · refine (sq_iota_quad_iff _ _).1 ⟨L, hLm, hLd, ?_⟩
      rw [← e1_resPoly_eq hK hπ hc ha]
      exact hLe
  · rintro ⟨hc, hne, hL⟩
    obtain ⟨a, ha⟩ := proj_surjective O 4 K c
    obtain ⟨L, hLm, hLd, hLe⟩ := (sq_iota_quad_iff _ _).2 hL
    exact ⟨hc, a, ha, L, hLm, hLd, by rw [e1_resPoly_eq hK hπ hc ha]; exact hLe⟩

/-- A genre box with pair-pinned membership is the union of its digit fibers; each
fiber contributes `q^(4K−8)`.  The shared engine for the two genre counts. -/
private theorem card_genre_box {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    (S : Set (Coeff O 4 K)) (P : Set (ResidueField O × ResidueField O))
    (hmem : ∀ c, c ∈ S ↔ c ∈ e1Box O K
      ∧ (resDig π 1 (c 2), resDig π 2 (c 0)) ∈ P)
    (hP : ∀ p ∈ P, p.2 ≠ 0) :
    Nat.card S = Nat.card P * residueCard O ^ (4 * K - 8) := by
  classical
  letI : Fintype (Coeff O 4 K) := Fintype.ofFinite _
  have hfin : P.Finite := Set.toFinite _
  rw [natCard_eq_sum_fiber S (fun c => (resDig π 1 (c 2), resDig π 2 (c 0)))
      hfin.toFinset
      (fun c hc => by
        rw [Set.Finite.mem_toFinset]
        exact ((hmem c).1 hc).2)]
  have hfib : ∀ p ∈ hfin.toFinset,
      Nat.card ((S ∩ (fun c => (resDig π 1 (c 2), resDig π 2 (c 0))) ⁻¹' {p}
          : Set (Coeff O 4 K)))
        = residueCard O ^ (4 * K - 8) := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    have hset : S ∩ (fun c => (resDig π 1 (c 2), resDig π 2 (c 0))) ⁻¹' {p}
        = e1Fiber π K p.1 p.2 := by
      ext c
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hcS, hΨ⟩
        have hbox := ((hmem c).1 hcS).1
        have hfibc := ((mem_e1Box_iff_fiber hK hπ c).1 hbox).2
        rw [show resDig π 1 (c 2) = p.1 from congrArg Prod.fst hΨ,
          show resDig π 2 (c 0) = p.2 from congrArg Prod.snd hΨ] at hfibc
        exact hfibc
      · intro hcF
        have hdig : (resDig π 1 (c 2), resDig π 2 (c 0)) = p := by
          obtain ⟨⟨-, hα⟩, -, ⟨-, hβ⟩, -⟩ := (mem_e1Fiber_iff c).1 hcF
          exact Prod.ext hβ hα
        have hbox : c ∈ e1Box O K := by
          rw [mem_e1Box_iff_fiber hK hπ]
          refine ⟨?_, ?_⟩
          · rw [show resDig π 2 (c 0) = p.2 from congrArg Prod.snd hdig]
            exact hP p hp
          · rw [show resDig π 1 (c 2) = p.1 from congrArg Prod.fst hdig,
              show resDig π 2 (c 0) = p.2 from congrArg Prod.snd hdig]
            exact hcF
        exact ⟨(hmem c).2 ⟨hbox, by rw [hdig]; exact hp⟩, hdig⟩
    rw [hset, card_e1Fiber hK hπ]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]

/-- ★★ **The irreducible-sector depth-0 count**: `N₂(q) · q^(4K−8)`. -/
theorem card_e1IrrBox_necklace {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    Nat.card (e1IrrBox (O := O) π K : Set (Coeff O 4 K))
      = Nat.card (IFCG4.IrredOfDeg (ResidueField O) 2)
          * residueCard O ^ (4 * K - 8) := by
  rw [card_genre_box hK hπ _ _ (mem_e1IrrBox_iff_pairs hK hπ)
    (fun p hp => irrPairs_snd_ne_zero hp), card_irrPairs]

/-- ★★ **The double-root-sector depth-0 count**: `(q−1) · q^(4K−8)`. -/
theorem card_e1DdBox {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    Nat.card (e1DdBox (O := O) π K : Set (Coeff O 4 K))
      = (residueCard O - 1) * residueCard O ^ (4 * K - 8) := by
  rw [card_genre_box hK hπ _ _ (mem_e1DdBox_iff_pairs hK hπ)
    (fun p hp => hp.1), card_ddPairs]
  rfl

/-- The genre partition, counted: the E1 cell is the exact sum of its three genres. -/
theorem card_e1Box_partition {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    Nat.card (e1Box O K : Set (Coeff O 4 K))
      = Nat.card (e1SplitBox (O := O) π K : Set (Coeff O 4 K))
        + Nat.card (e1IrrBox (O := O) π K : Set (Coeff O 4 K))
        + Nat.card (e1DdBox (O := O) π K : Set (Coeff O 4 K)) := by
  have h12 : Disjoint (e1SplitBox π K) (e1IrrBox π K) :=
    disjoint_e1SplitBox_e1IrrBox hK hπ
  have h13 : Disjoint (e1SplitBox π K) (e1DdBox π K) :=
    disjoint_e1SplitBox_e1DdBox hK hπ
  have h23 : Disjoint (e1IrrBox π K) (e1DdBox π K) :=
    disjoint_e1IrrBox_e1DdBox hK hπ
  rw [e1Box_eq_genres hK hπ, Nat.card_coe_set_eq,
    Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨h13, h23⟩) (Set.toFinite _)
      (Set.toFinite _),
    Set.ncard_union_eq h12 (Set.toFinite _) (Set.toFinite _),
    ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]

/-- ★ **The irreducible-sector count, CLOSED** (ER4's verdict target):
`2·#e1IrrBox = (q²−q)·q^(4K−8)`. -/
theorem card_e1IrrBox_closed {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    2 * Nat.card (e1IrrBox (O := O) π K : Set (Coeff O 4 K))
      = (residueCard O ^ 2 - residueCard O) * residueCard O ^ (4 * K - 8) := by
  letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
  have hqcard : Fintype.card (ResidueField O) = residueCard O :=
    Nat.card_eq_fintype_card.symm
  have hIrr := two_mul_card_irredOfDeg_two (ResidueField O)
  rw [hqcard] at hIrr
  rw [card_e1IrrBox_necklace hK hπ, ← Nat.mul_assoc, hIrr]

/-- ★ **The split-sector count, CLOSED** (ER4's verdict target):
`2·#e1SplitBox = (q−1)(q−2)·q^(4K−8)`. -/
theorem card_e1SplitBox_closed {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    2 * Nat.card (e1SplitBox (O := O) π K : Set (Coeff O 4 K))
      = (residueCard O - 1) * (residueCard O - 2) * residueCard O ^ (4 * K - 8) := by
  letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
  have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
  have hqcard : Fintype.card (ResidueField O) = residueCard O :=
    Nat.card_eq_fintype_card.symm
  obtain ⟨E, h8, h7⟩ : ∃ E, 4 * K - 8 = E ∧ 4 * K - 7 = E + 1 :=
    ⟨4 * K - 8, rfl, by omega⟩
  have hpart := card_e1Box_partition (π := π) hK hπ
  rw [card_e1Box (O := O) hK, card_e1IrrBox_necklace hK hπ, card_e1DdBox hK hπ,
    h8, h7] at hpart
  have hIrr := two_mul_card_irredOfDeg_two (ResidueField O)
  rw [hqcard] at hIrr
  have hpartZ := congrArg (Nat.cast : ℕ → ℤ) hpart
  have hIrrZ := congrArg (Nat.cast : ℕ → ℤ) hIrr
  have h1q : 1 ≤ residueCard O := by omega
  have hqsq : residueCard O ≤ residueCard O ^ 2 := Nat.le_self_pow (by norm_num) _
  push_cast [Nat.cast_sub h1q] at hpartZ
  push_cast [Nat.cast_sub hqsq] at hIrrZ
  have hgoalZ : ((2 * Nat.card (e1SplitBox (O := O) π K : Set (Coeff O 4 K)) : ℕ) : ℤ)
      = (((residueCard O - 1) * (residueCard O - 2)
          * residueCard O ^ (4 * K - 8) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1q, Nat.cast_sub hq2]
    rw [h8]
    linear_combination (-2 : ℤ) * hpartZ - ((residueCard O : ℤ)) ^ E * hIrrZ
  exact_mod_cast hgoalZ

end GenreCounts

/-! ## §6 — the two depth-0 box limits and the rewired census front -/

section Limits

open Uniformity.Density.IFCG34 in
/-- ★★ **The irreducible-sector depth-0 box limit** (ER4's named premise, CLOSED):
the family is constant `N₂(q)/q⁸` — numerator IFCG19's necklace polynomial. -/
theorem zcURLim_e1IrrFam : ZcURLim e1IrrFam := by
  refine ⟨necklacePoly 2, Polynomial.X ^ 8, pow_ne_zero _ Polynomial.X_ne_zero, ?_⟩
  intro O _ _ _ _ _
  letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
  have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
  have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hden : (Polynomial.X ^ 8 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) ≠ 0 := by
    rw [Polynomial.eval_pow, Polynomial.eval_X]
    exact pow_ne_zero _ hqQ
  refine ⟨hden, ?_⟩
  intro π hπ
  have hqcard : residueCard O = Fintype.card (ResidueField O) := Nat.card_eq_fintype_card
  have hnum : (necklacePoly 2).eval ((residueCard O : ℕ) : ℚ)
      = ((Nat.card (IFCG4.IrredOfDeg (ResidueField O) 2) : ℕ) : ℚ) := by
    rw [hqcard]
    exact necklacePoly_eval_card (ResidueField O) 2 (by norm_num)
  have hval : ∀ M : ℕ, e1IrrFam O π M
      = (((necklacePoly 2).eval ((residueCard O : ℕ) : ℚ)
          / (Polynomial.X ^ 8 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) := by
    intro M
    have hK : 3 ≤ M + 4 := by omega
    unfold e1IrrFam
    rw [card_e1IrrBox_necklace hK hπ, hnum, Polynomial.eval_pow, Polynomial.eval_X]
    have hsplit : 4 * (M + 4) = (4 * (M + 4) - 8) + 8 := by omega
    rw [hsplit, pow_add]
    have hb : ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4) - 8) ≠ 0 := pow_ne_zero _ hqR
    push_cast
    field_simp
  exact Filter.Tendsto.congr (fun M => (hval M).symm) tendsto_const_nhds

open Uniformity.Density.IFCG34 in
/-- ★★ **The split-sector depth-0 box limit** (ER4's named premise, CLOSED): the family
is constant `(q−1)(q−2)/(2q⁸)` — written through the genre partition as
`((X−1)X − N₂ − (X−1))/X⁸`. -/
theorem zcURLim_e1SplitFam : ZcURLim e1SplitFam := by
  refine ⟨(Polynomial.X - 1) * Polynomial.X - necklacePoly 2 - (Polynomial.X - 1),
    Polynomial.X ^ 8, pow_ne_zero _ Polynomial.X_ne_zero, ?_⟩
  intro O _ _ _ _ _
  letI : Fintype (ResidueField O) := Fintype.ofFinite (ResidueField O)
  have hq2 : 2 ≤ residueCard O := two_le_residueCard (O := O)
  have hqQ : ((residueCard O : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqR : ((residueCard O : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hden : (Polynomial.X ^ 8 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) ≠ 0 := by
    rw [Polynomial.eval_pow, Polynomial.eval_X]
    exact pow_ne_zero _ hqQ
  refine ⟨hden, ?_⟩
  intro π hπ
  have hqcard : residueCard O = Fintype.card (ResidueField O) := Nat.card_eq_fintype_card
  have hnum : (necklacePoly 2).eval ((residueCard O : ℕ) : ℚ)
      = ((Nat.card (IFCG4.IrredOfDeg (ResidueField O) 2) : ℕ) : ℚ) := by
    rw [hqcard]
    exact necklacePoly_eval_card (ResidueField O) 2 (by norm_num)
  have hval : ∀ M : ℕ, e1SplitFam O π M
      = ((((Polynomial.X - 1) * Polynomial.X - necklacePoly 2
              - (Polynomial.X - 1)).eval ((residueCard O : ℕ) : ℚ)
          / (Polynomial.X ^ 8 : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) := by
    intro M
    have hK : 3 ≤ M + 4 := by omega
    obtain ⟨E, h8, h7, h0⟩ : ∃ E, 4 * (M + 4) - 8 = E ∧ 4 * (M + 4) - 7 = E + 1
        ∧ 4 * (M + 4) = E + 8 :=
      ⟨4 * (M + 4) - 8, rfl, by omega, by omega⟩
    have hpart := card_e1Box_partition (π := π) hK hπ
    rw [card_e1Box (O := O) hK, card_e1IrrBox_necklace hK hπ, card_e1DdBox hK hπ,
      h8, h7] at hpart
    have hpartR := congrArg (Nat.cast : ℕ → ℝ) hpart
    push_cast [Nat.cast_sub (show 1 ≤ residueCard O by omega)] at hpartR
    have hS : (Nat.card (e1SplitBox (O := O) π (M + 4) : Set (Coeff O 4 (M + 4))) : ℝ)
        = ((((residueCard O : ℕ) : ℝ) - 1) * ((residueCard O : ℕ) : ℝ)
              - (Nat.card (IFCG4.IrredOfDeg (ResidueField O) 2) : ℝ)
              - (((residueCard O : ℕ) : ℝ) - 1))
            * ((residueCard O : ℕ) : ℝ) ^ E := by
      linear_combination (-1 : ℝ) * hpartR
    unfold e1SplitFam
    rw [h0, Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, hnum,
      Polynomial.eval_pow, Polynomial.eval_X]
    push_cast
    rw [hS, pow_add]
    have hb : ((residueCard O : ℕ) : ℝ) ^ E ≠ 0 := pow_ne_zero _ hqR
    field_simp
  exact Filter.Tendsto.congr (fun M => (hval M).symm) tendsto_const_nhds

open Uniformity.Density.IFCG34 in
/-- The `∀ σ` split-sector decided family, UNCONDITIONALLY: the split box is
`{(2,1),(2,1)}`-decided, so the family is the full box at `ramPairType` and empty
elsewhere. -/
theorem zcURLim_e1SplitDecFam (σ : FactorizationType) :
    ZcURLim (e1SplitDecFam σ) := by
  by_cases hσ : σ = ramPairType
  · subst hσ
    refine zcURLim_e1SplitFam.congr ?_
    intro O _ _ _ _ _ π hπ M
    unfold e1SplitFam e1SplitDecFam
    rw [decided_inter_e1Split_eq_self (show 3 ≤ M + 4 by omega) hπ]
  · refine ZcURLim_zero.congr ?_
    intro O _ _ _ _ _ π hπ M
    show (0 : ℝ) = e1SplitDecFam σ O π M
    unfold e1SplitDecFam
    rw [decided_inter_e1Split_eq_empty (show 3 ≤ M + 4 by omega) hπ hσ,
      Nat.card_coe_set_eq, Set.ncard_empty, Nat.cast_zero, zero_div]

open Uniformity.Density.IFCG34 in
/-- The `∀ σ` irreducible-sector decided family, under the named leaf: full box at
`{(2,2)}`, empty elsewhere. -/
theorem zcURLim_e1IrrDecFam (hL : E1IrrLeafDecision) (σ : FactorizationType) :
    ZcURLim (e1IrrDecFam σ) := by
  by_cases h22 : σ = type22
  · subst h22
    refine zcURLim_e1IrrFam.congr ?_
    intro O _ _ _ _ _ π hπ M
    unfold e1IrrFam e1IrrDecFam
    rw [decided_inter_e1Irr_of_leaf hL (show 3 ≤ M + 4 by omega) hπ]
  · by_cases h41 : σ = type41
    · subst h41
      refine ZcURLim_zero.congr ?_
      intro O _ _ _ _ _ π hπ M
      show (0 : ℝ) = e1IrrDecFam type41 O π M
      unfold e1IrrDecFam
      rw [decided41_inter_e1Irr_of_leaf hL (show 3 ≤ M + 4 by omega) hπ,
        Nat.card_coe_set_eq, Set.ncard_empty, Nat.cast_zero, zero_div]
    · refine ZcURLim_zero.congr ?_
      intro O _ _ _ _ _ π hπ M
      show (0 : ℝ) = e1IrrDecFam σ O π M
      unfold e1IrrDecFam
      rw [decided_inter_e1Irr_eq_empty (show 3 ≤ M + 4 by omega) hπ h22 h41,
        Nat.card_coe_set_eq, Set.ncard_empty, Nat.cast_zero, zero_div]

end Limits

section Laws

open Uniformity.Density.IFCG34

/-- ★★ **The `{(2,1),(2,1)}` law, REWIRED**: the split-sector premise is closed — only
the two recursion terms (double-root + E2) survive. -/
theorem coneRemainderLaw_four_ramPair
    (h2 : ZcURLim (e1DdDecFam ramPairType)) (h3 : ZcURLim (e2DecFam ramPairType)) :
    ConeRemainderLaw 4 ramPairType :=
  coneRemainderLaw_four_ramPair_of_sectors zcURLim_e1SplitFam h2 h3

/-- ★★ **The `{(2,2)}` law, REWIRED**: the irreducible-sector premise is closed — only
the named leaf + the double-root recursion term survive. -/
theorem coneRemainderLaw_four_type22 (hL : E1IrrLeafDecision)
    (h2 : ZcURLim (e1DdDecFam type22)) : ConeRemainderLaw 4 type22 :=
  coneRemainderLaw_four_type22_of_sectors hL zcURLim_e1IrrFam h2

open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG25 (UnramifiedBlockBridge)

/-- ★★★ **THE CENSUS FRONT, REWIRED** (charge item 3): with both depth-0 box limits
closed, the all-degree decided slice rests on EXACTLY (a) the named leaf
`E1IrrLeafDecision`, (b) the two `∀ σ` recursion families (double-root order-2 + E2
mixed-system), (c) the `e ≥ 5` ramified remainder laws, and (d) the block bridges. -/
theorem decidedSliceAt_all_of_recursion_limits (hL : E1IrrLeafDecision)
    (hDd : ∀ σ : FactorizationType, ZcURLim (e1DdDecFam σ))
    (hE2 : ∀ σ : FactorizationType, ZcURLim (e2DecFam σ))
    (hR : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ConeRemainderLaw e σ)
    (hBr : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  decidedSliceAt_all_of_sector_limits (fun σ => zcURLim_e1SplitDecFam σ)
    (fun σ => zcURLim_e1IrrDecFam hL σ) hDd hE2 hR hBr

end Laws

end Uniformity.Density.IFCG36

end

/-! ## AXCHECK FOOTER — §§1,3,4,5-counting expect Lean core
`{propext, Classical.choice, Quot.sound}`; the resPoly-consuming bridge and the
limit/law sections expect Lean core PLUS exactly the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42), inherited through IFCG34.
The C.33 cites must NOT occur. -/

#print axioms Uniformity.Density.IFCG36.resDig_mk
#print axioms Uniformity.Density.IFCG36.card_setOf_resDig
#print axioms Uniformity.Density.IFCG36.resOrd_eq_iff_resDig
#print axioms Uniformity.Density.IFCG36.e1_resPoly_eq
#print axioms Uniformity.Density.IFCG36.resIota_bijective
#print axioms Uniformity.Density.IFCG36.card_irrPairs
#print axioms Uniformity.Density.IFCG36.card_ddPairs
#print axioms Uniformity.Density.IFCG36.card_e1Fiber
#print axioms Uniformity.Density.IFCG36.mem_e1Box_iff_fiber
#print axioms Uniformity.Density.IFCG36.card_e1IrrBox_necklace
#print axioms Uniformity.Density.IFCG36.card_e1DdBox
#print axioms Uniformity.Density.IFCG36.card_e1Box_partition
#print axioms Uniformity.Density.IFCG36.necklacePoly_two_eval
#print axioms Uniformity.Density.IFCG36.two_mul_card_irredOfDeg_two
#print axioms Uniformity.Density.IFCG36.card_e1IrrBox_closed
#print axioms Uniformity.Density.IFCG36.card_e1SplitBox_closed
#print axioms Uniformity.Density.IFCG36.zcURLim_e1IrrFam
#print axioms Uniformity.Density.IFCG36.zcURLim_e1SplitFam
#print axioms Uniformity.Density.IFCG36.zcURLim_e1SplitDecFam
#print axioms Uniformity.Density.IFCG36.zcURLim_e1IrrDecFam
#print axioms Uniformity.Density.IFCG36.coneRemainderLaw_four_ramPair
#print axioms Uniformity.Density.IFCG36.coneRemainderLaw_four_type22
#print axioms Uniformity.Density.IFCG36.decidedSliceAt_all_of_recursion_limits
