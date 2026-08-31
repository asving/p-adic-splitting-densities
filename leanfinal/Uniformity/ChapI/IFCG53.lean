/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG36
import Uniformity.ChapB.B60
import Uniformity.Density.Gates

/-!
# Uniformity.ChapI.IFCG53 — THE E2 DEPTH-0 CLOSURE: the three `e2DecFam` limits on the
named dd-recursion terms alone, and the FULL `∀ σ` E2 front

**UNIT E2L** (wave C, 2026-08-31).  The last mass-4 counting sector: `e2Box`
(`v₀ ≥ 3, v₁ ≥ 2, v₂ = 1` pinned, `v₃ ≥ 1`, count `(q−1)q^(4K−8)`), where every lift
splits as the `[2,4]` slope-`1/2` block `F` (a `(2,1)` ramified quadratic) times a monic
quadratic cofactor `R` (IFCG34 §5).  This file closes the DEPTH-0 layer of ER4's E2
genre plan and fires the `ZcURLim (e2DecFam σ)` families.

## The genre partition (uniform in `q` AND in the corner depth)

With `(v₀', v₁') := (resOrd (c 0), resOrd (c 1))` free (the corner is UNBOUNDED — unlike
E1's pinned `v₀ = 2`, the E2 depth-0 census is an infinite geometric family):

* **(a) `aBox t`** (`v₀' = 2t` exact, `t ≥ 2`, `v₁' ≥ t+1`): fractional `[0,2]` face of
  slope `(2t−1)/2` ⇒ the cofactor is `(2t−1,2)`-pure ⇒ DECIDED `{(2,1),(2,1)}`.
  Stratum count `(q−1)²·q^(4K−3t−5)`.
* **(b) `bBox v`** (`v₁' = v` exact, `v ≥ 2`, `v₀' ≥ 2v`): broken polygon, two integral
  width-1 faces ⇒ two `(1,1)` linears ⇒ DECIDED `{(1,1),(1,1),(2,1)}`.  Stratum count
  `(q−1)²·q^(4K−3v−4)`.  NO boundary: `2v₁' ≤ v₀' ≤ K` is automatic.
* **(c) `cBox s P`** (`v₀' = 2s+1` exact, `s ≥ 1`, `v₁' ≥ s+1`): integral slope-`s`
  width-2 face; the cofactor's B.44-extracted reduction is the CLASS-DIGIT quadratic
  `Y² + (d₁/δ)Y + (d₀/δ)` (`δ = resDig π 1 (c 2)`, `d₁ = resDig π (s+1) (c 1)`,
  `d₀ = resDig π (2s+1) (c 0)`); trichotomy on the pair `(d₁/δ, d₀/δ)`:
  `splitPairs` ⇒ DECIDED `{(1,1),(1,1),(2,1)}` (Hensel split), `irrPairs` ⇒ DECIDED
  `{(1,2),(2,1)}` (the ℓ = 1 inert leaf — B.44 + CN-21, UNCONDITIONAL), `ddPairs` ⇒ the
  named recursion carrier `e2DdBox`.  Stratum counts `(q−1)·#P·q^(4K−3s−7)`.
* **Boundary `bdBox`** (`v₀' = K` invisible, `2v₁' ≥ K+1`): measure `≤ q^(−K) → 0`
  (squeezed; no undecidability proof needed).

Measure check: `(a)+(b)+(c-total) = (q−1)²(q^(−8)+q^(−7)+q^(−6))/(q³−1) = (q−1)q^(−8)`
`= measure(e2Box)` exactly.

## The decision mechanism (all-orders-uniform; NO residual multiplicativity)

Peel `F` by IFCG26's `exists_pure_factor_of_two_point_side` at the `[2,4]` face
(purity RETAINED — `exists_ramQuad_factor_of_e2` discards it); read the cofactor `R`'s
polygon off the four coefficient identities `a₀ = f₀r₀`, `a₁ = f₀r₁ + f₁r₀`,
`a₂ = f₀ + r₀ + f₁r₁`, `a₃ = f₁ + r₁` in digit currency (π-power factored forms,
`digAt_eq`/`digAt_eq_zero_iff`).  Genre (c) then goes through B.44's
`exists_scaleRoots_of_pure_integral`, whose digit clause hands the extracted `Ḡ`
coefficientwise; the residue-field trichotomy is IFCG36's `irrPairs`/`ddPairs` frame.

## The recursion fence (charge item 2's reach check — ANSWERED, negative at depth ≥ 1)

IFCG20's linear recentring PROVABLY misses `e2Box` (its range forces
`resOrd (c 2) ≥ 2` against the pinned `v₂ = 1`); IFCG43's `cellTransport` reaches the
counting/value layers of the mass-2 reduction but no decidedness transport is landed
(its honest-scope items 1+3).  So the dd sector enters as ONE new named family
`e2DdDecFam σ` (the exact analogue of ER4's `e1DdDecFam`), consumed only by the three
named σ; every OTHER σ closes at value `0` UNCONDITIONALLY (every lift's type is
`{(2,1)} + (quadratic type)` — three shapes only).

## Axiom fence

Lean core `{propext, Classical.choice, Quot.sound}` plus EXACTLY the owner-signed
gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42), inherited
through IFCG26's two-point-side peel — already on the E2 rows via IFCG34.  B.44/B.59/
B.60/CN-21/Hensel are all Lean-core.  The C.33 cites must NOT occur.  Zero sorries.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
-- the sector limit families must mirror `ZcURLim`'s binder list byte-for-byte
set_option linter.overlappingInstances false

noncomputable section

namespace Uniformity.Density.IFCG53

open IsLocalRing Polynomial Filter Topology
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFC7 (resOut mk_resOut)
open Uniformity.Density.IFCG17 (decidedAt_unique)
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply le_classNPSupport classNPSupport_le
  classCoeffVal_exact le_classCoeffVal_iff_dvd classCoeffVal_le classCoeffVal_eq_iff)
open Uniformity.Density.IFCG23 (npHgt_monicPoly_eq le_npHgt_monicPoly npHgt_monicPoly_top
  addVal_eq_of_pow_dvd_not_dvd)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ZcURLim_qmonomial ZcURLim_sum
  card_setOf_le_resOrd card_setOf_resOrd_eq card_pi_set mem_stratum_X_pow_iff
  coneRemainderCount ConeRemainderLaw)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains
  exists_pure_factor_of_two_point_side dvd_natDegree_of_isPure
  irreducible_of_isPure_natDegree_eq monicFactors_of_irreducible
  exists_mem_monicFactors mem_sideSet_of_onSide irreducible_of_monic_natDegree_one)
open Uniformity.Density.IFCG31 (mixedType4 ramPairType)
open Uniformity.Density.IFCG34 (e2Box mem_e2Box_iff card_e2Box type22 type41
  splitTailType inertTailType e2DecFam exists_ramQuad_factor_of_e2
  monic_quadratic_trichotomy coneRemainderLaw_four_of_odd_member E1IrrLeafDecision
  e1SplitDecFam e1IrrDecFam e1DdDecFam)
open Uniformity.Density.IFCG36 (resDig resDig_mk card_setOf_resDig resOrd_eq_iff_resDig
  irrPairs ddPairs card_irrPairs card_ddPairs irrPairs_snd_ne_zero
  monic_quadratic_eq_coeffs two_mul_card_irredOfDeg_two necklacePoly_two_eval)
open Uniformity.Density.IFCG19 (necklacePoly necklacePoly_eval_card)

attribute [local instance] Classical.propDecidable

/-! ## §0 — the coefficient kit (quadratic/quartic coefficient reads, any CommRing) -/

section CoeffKit

variable {S : Type*} [CommRing S] [Nontrivial S]

-- IFCG36's private quad helpers, reproduced over a CommRing (the sanctioned replay).
private theorem quad_coeff_one (b a : S) :
    (X ^ 2 + Polynomial.C b * X + Polynomial.C a : Polynomial S).coeff 1 = b := by
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C]

private theorem quad_coeff_zero (b a : S) :
    (X ^ 2 + Polynomial.C b * X + Polynomial.C a : Polynomial S).coeff 0 = a := by
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C]

private theorem quad_natDegree (b a : S) :
    (X ^ 2 + Polynomial.C b * X + Polynomial.C a : Polynomial S).natDegree = 2 := by
  compute_degree!

private theorem quad_monic (b a : S) :
    (X ^ 2 + Polynomial.C b * X + Polynomial.C a : Polynomial S).Monic := by
  show (X ^ 2 + Polynomial.C b * X + Polynomial.C a : Polynomial S).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, quad_natDegree]
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]

/-- Monic quadratic reconstruction (IFCG36's, replayed over a CommRing). -/
private theorem monic_quad_eq_coeffs {G : Polynomial S} (hm : G.Monic)
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

private theorem quartic_coeff_zero (d₃ d₂ d₁ d₀ : S) :
    (X ^ 4 + Polynomial.C d₃ * X ^ 3 + Polynomial.C d₂ * X ^ 2
      + Polynomial.C d₁ * X + Polynomial.C d₀ : Polynomial S).coeff 0 = d₀ := by
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C]

private theorem quartic_coeff_one (d₃ d₂ d₁ d₀ : S) :
    (X ^ 4 + Polynomial.C d₃ * X ^ 3 + Polynomial.C d₂ * X ^ 2
      + Polynomial.C d₁ * X + Polynomial.C d₀ : Polynomial S).coeff 1 = d₁ := by
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C]

private theorem quartic_coeff_two (d₃ d₂ d₁ d₀ : S) :
    (X ^ 4 + Polynomial.C d₃ * X ^ 3 + Polynomial.C d₂ * X ^ 2
      + Polynomial.C d₁ * X + Polynomial.C d₀ : Polynomial S).coeff 2 = d₂ := by
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C]

private theorem quartic_coeff_three (d₃ d₂ d₁ d₀ : S) :
    (X ^ 4 + Polynomial.C d₃ * X ^ 3 + Polynomial.C d₂ * X ^ 2
      + Polynomial.C d₁ * X + Polynomial.C d₀ : Polynomial S).coeff 3 = d₃ := by
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C]

/-- The product of two monic quadratics, coefficientwise: the four identities
`(FR)₀ = f₀r₀`, `(FR)₁ = f₀r₁ + f₁r₀`, `(FR)₂ = f₀ + f₁r₁ + r₀`, `(FR)₃ = f₁ + r₁`. -/
private theorem coeff_mul_quadratics {F R : Polynomial S} (hF : F.Monic) (hR : R.Monic)
    (hFd : F.natDegree = 2) (hRd : R.natDegree = 2) :
    (F * R).coeff 0 = F.coeff 0 * R.coeff 0
    ∧ (F * R).coeff 1 = F.coeff 0 * R.coeff 1 + F.coeff 1 * R.coeff 0
    ∧ (F * R).coeff 2 = F.coeff 0 + F.coeff 1 * R.coeff 1 + R.coeff 0
    ∧ (F * R).coeff 3 = F.coeff 1 + R.coeff 1 := by
  have hprod : F * R
      = X ^ 4 + Polynomial.C (F.coeff 1 + R.coeff 1) * X ^ 3
        + Polynomial.C (F.coeff 0 + F.coeff 1 * R.coeff 1 + R.coeff 0) * X ^ 2
        + Polynomial.C (F.coeff 0 * R.coeff 1 + F.coeff 1 * R.coeff 0) * X
        + Polynomial.C (F.coeff 0 * R.coeff 0) := by
    conv_lhs => rw [monic_quad_eq_coeffs hF hFd, monic_quad_eq_coeffs hR hRd]
    push_cast [Polynomial.C_add, Polynomial.C_mul]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hprod, quartic_coeff_zero]
  · rw [hprod, quartic_coeff_one]
  · rw [hprod, quartic_coeff_two]
  · rw [hprod, quartic_coeff_three]

end CoeffKit

/-! ## §1 — the depth-0 genre boxes (class-digit form) -/

section Boxes

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The split pair set**: monic quadratics `X² + βX + α` (as pairs `(β, α)`) with two
DISTINCT roots and nonzero constant term — the field-side split genre, complementing
IFCG36's `irrPairs`/`ddPairs` on `{α ≠ 0}`. -/
def splitPairs (F : Type*) [Field F] : Set (F × F) :=
  {p | p.2 ≠ 0 ∧ ∃ z₁ z₂ : F, z₁ ≠ z₂ ∧
    X ^ 2 + Polynomial.C p.1 * X + Polynomial.C p.2
      = (X - Polynomial.C z₁) * (X - Polynomial.C z₂)}

/-- **Genre (a)** — the fractional-corner stratum at `v₀ = 2t`: the `[0,2]` face has
slope `(2t−1)/2` (denominator 2), so the cofactor is a second `(2,1)` block. -/
def aBox (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K t : ℕ) : Set (Coeff O 4 K) :=
  {c | resOrd (c 0) = 2 * t ∧ t + 1 ≤ resOrd (c 1)
    ∧ resOrd (c 2) = 1 ∧ 1 ≤ resOrd (c 3)}

/-- **Genre (b)** — the broken-polygon stratum at `v₁ = v` exact, `v₀ ≥ 2v`: two
integral width-1 faces, two `(1,1)` linears. -/
def bBox (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K v : ℕ) : Set (Coeff O 4 K) :=
  {c | 2 * v ≤ resOrd (c 0) ∧ resOrd (c 1) = v
    ∧ resOrd (c 2) = 1 ∧ 1 ≤ resOrd (c 3)}

/-- The genre-(c) residual pair of a class at corner depth `2s+1`: the monic
normalization `(d₁/δ, d₀/δ)` of the width-2 face's digit triple. -/
def cPair (π : O) (s : ℕ) {K : ℕ} (c : Coeff O 4 K) :
    ResidueField O × ResidueField O :=
  (resDig π (s + 1) (c 1) / resDig π 1 (c 2),
   resDig π (2 * s + 1) (c 0) / resDig π 1 (c 2))

/-- **Genre (c)** — the integral-slope width-2-face stratum at `v₀ = 2s+1`, genre keyed
by the pair set `P` (split / irreducible / double-root). -/
def cBox (π : O) (K s : ℕ) (P : Set (ResidueField O × ResidueField O)) :
    Set (Coeff O 4 K) :=
  {c | resOrd (c 0) = 2 * s + 1 ∧ s + 1 ≤ resOrd (c 1)
    ∧ resOrd (c 2) = 1 ∧ 1 ≤ resOrd (c 3) ∧ cPair π s c ∈ P}

/-- **The boundary cell** — the invisible corner (`resOrd (c 0) = K`) above the chord:
the only part of `e2Box` outside the visible genre boxes.  Measure `≤ q^(−K)`. -/
def bdBox (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : ℕ) : Set (Coeff O 4 K) :=
  {c | K ≤ resOrd (c 0) ∧ K + 1 ≤ 2 * resOrd (c 1)
    ∧ resOrd (c 2) = 1 ∧ 1 ≤ resOrd (c 3)}

/-- **The named dd-recursion carrier**: the union of the double-root sub-boxes over all
visible corner depths — the E2 analogue of ER4's `e1DdBox`, and the ONE open premise
carrier of this file's laws. -/
def e2DdBox (π : O) (K : ℕ) : Set (Coeff O 4 K) :=
  ⋃ s ∈ Finset.filter (fun s => 1 ≤ s ∧ 2 * s + 1 < K) (Finset.range K),
    cBox π K s (ddPairs (ResidueField O))

end Boxes

/-! ## §1b — the field-side trichotomy partition on `{α ≠ 0}` -/

section PairTrichotomy

variable {F : Type*} [Field F]

theorem splitPairs_snd_ne_zero {p : F × F} (hp : p ∈ splitPairs F) : p.2 ≠ 0 := hp.1

theorem ddPairs_snd_ne_zero {p : F × F} (hp : p ∈ ddPairs F) : p.2 ≠ 0 := hp.1

/-- The three pair genres exhaust `{α ≠ 0}` (IFCG34's `monic_quadratic_trichotomy`,
read on the pair frame). -/
theorem pair_trichotomy {p : F × F} (hp : p.2 ≠ 0) :
    p ∈ splitPairs F ∨ p ∈ irrPairs F ∨ p ∈ ddPairs F := by
  rcases monic_quadratic_trichotomy (quad_monic p.1 p.2) (quad_natDegree p.1 p.2) with
    ⟨G, H, hGm, hHm, hGd, hHd, hcop, heq⟩ | hirr | ⟨L, hLm, hLd, hLe⟩
  · obtain ⟨g0, hG⟩ : ∃ g0, G = X + Polynomial.C g0 := ⟨G.coeff 0, hGm.eq_X_add_C hGd⟩
    obtain ⟨h0, hH⟩ : ∃ h0, H = X + Polynomial.C h0 := ⟨H.coeff 0, hHm.eq_X_add_C hHd⟩
    have hne : g0 ≠ h0 := by
      intro hgh
      have hGH : G = H := by rw [hG, hH, hgh]
      rw [hGH] at hcop
      have hu : IsUnit H := hcop.isUnit_of_dvd' dvd_rfl dvd_rfl
      exact Polynomial.not_isUnit_of_natDegree_pos H (by omega) hu
    refine Or.inl ⟨hp, -g0, -h0, by simpa using hne, ?_⟩
    rw [heq, hG, hH, map_neg, map_neg, sub_neg_eq_add, sub_neg_eq_add]
  · exact Or.inr (Or.inl hirr)
  · exact Or.inr (Or.inr ⟨hp, L, hLm, hLd, hLe⟩)

/-- Split excludes irreducible. -/
theorem disjoint_splitPairs_irrPairs : Disjoint (splitPairs F) (irrPairs F) := by
  rw [Set.disjoint_left]
  rintro p ⟨-, z₁, z₂, -, heq⟩ hirr
  have hirr' : Irreducible ((X - Polynomial.C z₁) * (X - Polynomial.C z₂)) := by
    rw [← heq]; exact hirr
  rcases hirr'.isUnit_or_isUnit rfl with h | h
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [Polynomial.natDegree_X_sub_C]; omega) h
  · exact Polynomial.not_isUnit_of_natDegree_pos _
      (by rw [Polynomial.natDegree_X_sub_C]; omega) h

/-- Split excludes double-root: evaluating the square shape at both roots forces the
roots equal. -/
theorem disjoint_splitPairs_ddPairs : Disjoint (splitPairs F) (ddPairs F) := by
  rw [Set.disjoint_left]
  rintro p ⟨-, z₁, z₂, hz, heq⟩ ⟨-, L, hLm, hLd, hLe⟩
  obtain ⟨t, hL⟩ : ∃ t, L = X + Polynomial.C t := ⟨L.coeff 0, hLm.eq_X_add_C hLd⟩
  have hev : ∀ z : F, (z - z₁) * (z - z₂) = (z + t) ^ 2 := by
    intro z
    have h := congrArg (Polynomial.eval z) (heq.symm.trans hLe)
    simpa [hL] using h
  have h1 : z₁ = -t := by
    have h := hev z₁
    simp only [sub_self, zero_mul] at h
    exact eq_neg_of_add_eq_zero_left (pow_eq_zero_iff (n := 2) (by omega) |>.1 h.symm)
  have h2 : z₂ = -t := by
    have h := hev z₂
    simp only [sub_self, mul_zero] at h
    exact eq_neg_of_add_eq_zero_left (pow_eq_zero_iff (n := 2) (by omega) |>.1 h.symm)
  exact hz (h1.trans h2.symm)

/-- Irreducible excludes double-root. -/
theorem disjoint_irrPairs_ddPairs : Disjoint (irrPairs F) (ddPairs F) := by
  rw [Set.disjoint_left]
  rintro p hirr ⟨-, L, hLm, hLd, hLe⟩
  have hirr' : Irreducible (L ^ 2) := by
    rw [← hLe]; exact hirr
  rw [sq] at hirr'
  rcases hirr'.isUnit_or_isUnit rfl with h | h <;>
    exact Polynomial.not_isUnit_of_natDegree_pos L (by omega) h

end PairTrichotomy

/-! ## §2 — the peel bank: the `[2,4]` block with its purity data retained -/

section Peel

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

-- IFCG34's private `e2_class_bank`, reproduced (the sanctioned replay).
private theorem e2_class_bank {K : ℕ} (hK : 3 ≤ K) {c : Coeff O 4 K}
    (hc : c ∈ e2Box O K) :
    classNPSupport c 1 2 = 4 ∧ NPAttains c 1 2 2 ∧ NPAttains c 1 2 4
      ∧ NPVisibleAt c 1 2 ∧ c ∈ levelZeroStratum O 4 K (X ^ 4) := by
  obtain ⟨h0, h1, h2, h3⟩ := (mem_e2Box_iff c).1 hc
  have hnp0 : 3 ≤ npHeight c 0 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (0 : ℕ) < 4)]
    exact h0
  have hnp1 : 2 ≤ npHeight c 1 := by
    unfold npHeight
    rw [dif_pos (by norm_num : (1 : ℕ) < 4)]
    exact h1
  have hnp2 : npHeight c 2 = 1 := by
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
  have hAt2 : NPAttains c 1 2 2 := ⟨by omega, by rw [hnp2, hsup]⟩
  have hAt4 : NPAttains c 1 2 4 := ⟨le_refl 4, by rw [hnp4, hsup]⟩
  have hvis : NPVisibleAt c 1 2 := by
    show classNPSupport c 1 2 < 2 * K
    rw [hsup]
    omega
  have hstr : c ∈ levelZeroStratum O 4 K (X ^ 4) := by
    refine (mem_stratum_X_pow_iff (by omega) c).2 ?_
    intro i
    fin_cases i
    · exact le_trans (by norm_num) h0
    · exact le_trans (by norm_num) h1
    · exact le_of_le_of_eq (by norm_num) h2.symm
    · exact h3
  exact ⟨hsup, hAt2, hAt4, hvis, hstr⟩

/-- ★ **The E2 peel** — the `[2,4]` block extraction WITH its data retained: every lift
of an `e2Box` class factors as `F · R` with `F` a monic `(1,2)`-pure quadratic
(irreducible, `efPair (2,1)`, constant coefficient `π·w` with `w` of nonzero digit,
`π ∣ F₁`) and `R` a monic quadratic cofactor.  (IFCG34's `exists_ramQuad_factor_of_e2`
discards the purity/valuation data; the genre decisions need it.) -/
private theorem e2_peel {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e2Box O K) {a : Fin 4 → O} (ha : proj O 4 K a = c) :
    ∃ F R : Polynomial O, F.Monic ∧ R.Monic ∧ Irreducible F ∧ efPair F = (2, 1)
      ∧ F.natDegree = 2 ∧ R.natDegree = 2 ∧ monicPoly a = F * R
      ∧ (∃ w : O, F.coeff 0 = π * w ∧ IsLocalRing.residue O w ≠ 0)
      ∧ π ∣ F.coeff 1 := by
  obtain ⟨h0, -, -, -⟩ := (mem_e2Box_iff c).1 hc
  obtain ⟨hsup, hAt2, hAt4, hvis, hstr⟩ := e2_class_bank hK hc
  obtain ⟨hO2, hsupp⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hAt2 ha
  obtain ⟨hO4, -⟩ := onSide_monicPoly_of_npAttains hπ (by norm_num) hvis hAt4 ha
  have hgm : (monicPoly a).Monic := monicPoly_monic a
  have hgdeg : (monicPoly a).natDegree = 4 := monicPoly_natDegree a
  have hsupp4 : suppVal X (monicPoly a) 1 2 = ((4 : ℕ) : ℕ∞) := by
    rw [hsupp, hsup]
  have htop : suppVal X (monicPoly a) 1 2 ≠ ⊤ := by
    rw [hsupp4]
    exact ENat.coe_ne_top _
  have hres : (monicPoly a).map (IsLocalRing.residue O) = X ^ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree]
    exact hstr a ha
  obtain ⟨F, R, hFm, hRm, hFp, hFdpos, heqFR⟩ :=
    exists_pure_factor_of_two_point_side hπ hgm hres (by norm_num) (by norm_num)
      (Nat.coprime_one_left 2) (show (2 : ℕ) < 4 by norm_num)
      (le_of_eq (monicPoly_natDegree a).symm) hO2 hO4 htop
  have hFdvd : 2 ∣ F.natDegree := dvd_natDegree_of_isPure hπ hFm (by norm_num)
    (Nat.coprime_one_left 2) hFp
  have hdegsum : F.natDegree + R.natDegree = 4 := by
    have h6 : (monicPoly a).natDegree = F.natDegree + R.natDegree := by
      rw [heqFR]
      exact Polynomial.natDegree_mul hFm.ne_zero hRm.ne_zero
    omega
  -- the pure block cannot be the whole quartic: `v₀ ≥ 3` breaks `OnSide` at `0`
  have hFdeg2 : F.natDegree = 2 := by
    rcases (by omega : F.natDegree = 2 ∨ F.natDegree = 4) with h24 | h24
    · exact h24
    exfalso
    have hRdeg0 : R.natDegree = 0 := by omega
    have hR1 : R = 1 := (Polynomial.Monic.natDegree_eq_zero hRm).mp hRdeg0
    have hgF : monicPoly a = F := by rw [heqFR, hR1, mul_one]
    have hpure' : IsPure X (monicPoly a) 1 2 := by
      rw [hgF]
      exact hFp
    have hO0 : OnSide X (monicPoly a) 1 2 0 := hpure'.1
    have hfin : npHgt X (monicPoly a) 0 ≠ ⊤ :=
      npHgt_ne_top_of_onSide (by norm_num) htop hO0
    obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hfin
    have hw' : npHgt X (monicPoly a) 0 = ((w : ℕ) : ℕ∞) := by
      have h6 : ((w : ℕ) : ℕ∞) = npHgt X (monicPoly a) 0 := hw
      exact h6.symm
    have hOn : (2 : ℕ) • npHgt X (monicPoly a) 0 + ((1 * 0 : ℕ) : ℕ∞)
        = suppVal X (monicPoly a) 1 2 := hO0
    rw [hw', hsupp4, nsmul_eq_mul, ← Nat.cast_ofNat, ← Nat.cast_mul, ← Nat.cast_add,
      Nat.cast_inj] at hOn
    have hge3 : ((3 : ℕ) : ℕ∞) ≤ npHgt X (monicPoly a) 0 := by
      refine le_trans ?_ (le_npHgt_monicPoly hπ ha (by norm_num : (0 : ℕ) < 4))
      exact_mod_cast h0
    rw [hw', Nat.cast_le] at hge3
    omega
  obtain ⟨hFirr, hFef⟩ := irreducible_of_isPure_natDegree_eq hπ hFm (by norm_num)
    (Nat.coprime_one_left 2) hFp hFdeg2
  -- the pure block's own side data: `suppVal F = 2`, left height `1`, middle ≥ 1
  have hFtop : npHgt X F 2 = ((0 : ℕ) : ℕ∞) := by
    rw [npHgt_X]
    have hc2 : F.coeff 2 = 1 := by
      have h6 := hFm.coeff_natDegree
      rwa [hFdeg2] at h6
    rw [hc2]
    simp [(IsDiscreteValuationRing.addVal O).map_one]
  have hOdF : OnSide X F 1 2 2 := by
    have h6 := hFp.2
    rwa [Polynomial.natDegree_X, hFdeg2, Nat.div_one] at h6
  have hsuppF : suppVal X F 1 2 = ((2 : ℕ) : ℕ∞) := by
    have h6 : (2 : ℕ) • npHgt X F 2 + ((1 * 2 : ℕ) : ℕ∞) = suppVal X F 1 2 := hOdF
    rw [hFtop] at h6
    rw [← h6]
    simp
  have hFsuppTop : suppVal X F 1 2 ≠ ⊤ := by
    rw [hsuppF]
    exact ENat.coe_ne_top _
  have hO0F : OnSide X F 1 2 0 := hFp.1
  have hFfin : npHgt X F 0 ≠ ⊤ := npHgt_ne_top_of_onSide (by norm_num) hFsuppTop hO0F
  obtain ⟨H₀, hH₀'⟩ := WithTop.ne_top_iff_exists.mp hFfin
  have hH₀ : npHgt X F 0 = ((H₀ : ℕ) : ℕ∞) := hH₀'.symm
  have hnatF : 2 * H₀ + 1 * 0 = 2 * 0 + 1 * 2 := onSide_nat_eq hH₀ hFtop hO0F hOdF
  have hH₀1 : H₀ = 1 := by omega
  -- `F₀ = π·w` with a nonzero digit
  have hvalF0 : (IsDiscreteValuationRing.addVal O) (F.coeff 0) = ((1 : ℕ) : ℕ∞) := by
    rw [← npHgt_X, hH₀, hH₀1]
  have hdvdF0 : π ^ 1 ∣ F.coeff 0 := by
    rw [Uniformity.Hensel.pow_dvd_iff_le_addVal hπ, hvalF0]
  have hnotF0 : ¬ π ^ 2 ∣ F.coeff 0 := by
    rw [Uniformity.Hensel.pow_dvd_iff_le_addVal hπ, hvalF0]
    intro h6
    exact absurd (by exact_mod_cast h6) (by omega)
  obtain ⟨w, hw⟩ := hdvdF0
  rw [pow_one] at hw
  have hdvd1 : π ^ 1 ∣ F.coeff 0 := ⟨w, by rw [pow_one]; exact hw⟩
  have hwne : IsLocalRing.residue O w ≠ 0 := by
    have h6 : digAt π 1 (F.coeff 0) = IsLocalRing.residue O w :=
      digAt_eq hπ (by rw [hw, pow_one])
    intro h7
    rw [h7] at h6
    have h8 : π ^ (1 + 1) ∣ F.coeff 0 := (digAt_eq_zero_iff hπ hdvd1).1 h6
    exact hnotF0 (by simpa using h8)
  -- `π ∣ F₁` from the above-side inequality at abscissa 1
  have hleF1 : suppVal X F 1 2 ≤ (2 : ℕ) • npHgt X F 1 + ((1 * 1 : ℕ) : ℕ∞) := by
    unfold suppVal
    exact Finset.inf_le (by rw [hFdeg2]; norm_num)
  have hdvdF1 : π ∣ F.coeff 1 := by
    rw [hsuppF, npHgt_X] at hleF1
    have h1le : ((1 : ℕ) : ℕ∞) ≤ (IsDiscreteValuationRing.addVal O) (F.coeff 1) := by
      by_contra hno
      have h6 : (IsDiscreteValuationRing.addVal O) (F.coeff 1) = 0 :=
        Order.lt_one_iff.mp (by exact_mod_cast lt_of_not_ge hno)
      rw [h6] at hleF1
      simp at hleF1
    have h7 : π ^ 1 ∣ F.coeff 1 :=
      (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).2 h1le
    simpa using h7
  exact ⟨F, R, hFm, hRm, hFirr, hFef, hFdeg2, by omega, heqFR, ⟨w, hw, hwne⟩, hdvdF1⟩

end Peel

/-! ## §3 — the genre decisions (all corner depths at once) -/

section Decisions

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

-- π is prime, and units are prime-free: the two peel facts used everywhere below.
private theorem prime_of_irr {π : O} (hπ : Irreducible π) : Prime π :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp hπ

private theorem not_dvd_of_residue_ne_zero {π w : O} (hπ : Irreducible π)
    (hw : IsLocalRing.residue O w ≠ 0) : ¬ π ∣ w := by
  rintro ⟨u, rfl⟩
  apply hw
  have hπ0 : IsLocalRing.residue O π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2
      ((IsLocalRing.mem_maximalIdeal π).2 (mem_nonunits_iff.2 hπ.not_isUnit))
  rw [map_mul, hπ0, zero_mul]

/-- ★ **The genre-(a) decision, ALL fractional corner depths at once**: a class with
`v₀ = 2t` exact (visible), `v₁ ≥ t+1`, `v₂ = 1`, `v₃ ≥ 1` is DECIDED `{(2,1),(2,1)}` —
the cofactor is `(2t−1, 2)`-pure of degree 2, a second ramified quadratic. -/
theorem decidedAt_aBox {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) {t : ℕ}
    (ht : 2 ≤ t) (htK : 2 * t < K) {c : Coeff O 4 K} (hc : c ∈ aBox O K t) :
    DecidedAt O 4 ramPairType K c := by
  obtain ⟨h0, h1, h2, h3⟩ := hc
  intro a ha
  have hce2 : c ∈ e2Box O K := (mem_e2Box_iff c).2 ⟨by omega, by omega, h2, h3⟩
  obtain ⟨F, R, hFm, hRm, hFirr, hFef, hFdeg, hRdeg, heqFR, ⟨w, hw, hwne⟩, hf1⟩ :=
    e2_peel hK hπ hce2 ha
  obtain ⟨u1, hu1⟩ := hf1
  obtain ⟨hid0, hid1, hid2, hid3⟩ := coeff_mul_quadratics hFm hRm hFdeg hRdeg
  have hπw : ¬ π ∣ w := not_dvd_of_residue_ne_zero hπ hwne
  have hpr : Prime π := prime_of_irr hπ
  -- the lift coefficient identities
  have hpc0 : (monicPoly a).coeff 0 = a 0 :=
    monicPoly_coeff_lt a (show (0 : ℕ) < 4 by norm_num)
  have hpc1 : (monicPoly a).coeff 1 = a 1 :=
    monicPoly_coeff_lt a (show (1 : ℕ) < 4 by norm_num)
  have hA0 : a 0 = π * (w * R.coeff 0) := by
    have h := hid0
    rw [← heqFR, hpc0, hw] at h
    rw [h]; ring
  have hA1 : a 1 = π * (w * R.coeff 1) + π * (u1 * R.coeff 0) := by
    have h := hid1
    rw [← heqFR, hpc1, hw, hu1] at h
    rw [h]; ring
  -- exact valuation of `a 0`, lower bound on `a 1`
  have hexact0 : π ^ (2 * t) ∣ a 0 ∧ ¬ π ^ (2 * t + 1) ∣ a 0 := by
    have h := classCoeffVal_exact hπ ha (i := 0)
      (show classCoeffVal c 0 < K by show resOrd (c 0) < K; omega)
    rwa [show classCoeffVal c 0 = 2 * t from h0] at h
  have hdvd1a : π ^ (t + 1) ∣ a 1 := by
    refine (le_classCoeffVal_iff_dvd hπ (by omega) ha 1).1 ?_
    show t + 1 ≤ resOrd (c 1)
    exact h1
  -- the cofactor's constant coefficient: exactly `π^(2t−1)`
  have hr0dvd : π ^ (2 * t - 1) ∣ R.coeff 0 := by
    have h6 : π ^ (2 * t) ∣ π * (w * R.coeff 0) := hA0 ▸ hexact0.1
    have h7 : π * π ^ (2 * t - 1) ∣ π * (w * R.coeff 0) := by
      rw [show π * π ^ (2 * t - 1) = π ^ (2 * t) from by
        rw [← pow_succ']; congr 1; omega]
      exact h6
    have h8 : π ^ (2 * t - 1) ∣ w * R.coeff 0 :=
      (mul_dvd_mul_iff_left (hπ.ne_zero)).1 h7
    exact hpr.pow_dvd_of_dvd_mul_left _ hπw h8
  have hr0not : ¬ π ^ (2 * t) ∣ R.coeff 0 := by
    intro h6
    apply hexact0.2
    rw [hA0]
    have h7 : π ^ (2 * t) ∣ w * R.coeff 0 := Dvd.dvd.mul_left h6 w
    have h8 : π * π ^ (2 * t) ∣ π * (w * R.coeff 0) := mul_dvd_mul_left π h7
    rwa [show π * π ^ (2 * t) = π ^ (2 * t + 1) from by rw [← pow_succ']] at h8
  -- the cofactor's middle coefficient: at least `π^t`
  have hr1dvd : π ^ t ∣ R.coeff 1 := by
    have hsub : π * (w * R.coeff 1) = a 1 - π * (u1 * R.coeff 0) := by
      rw [hA1]; ring
    have h6 : π ^ (t + 1) ∣ π * (u1 * R.coeff 0) := by
      have h7 : π ^ (2 * t - 1) ∣ u1 * R.coeff 0 := Dvd.dvd.mul_left hr0dvd u1
      have h8 : π * π ^ (2 * t - 1) ∣ π * (u1 * R.coeff 0) := mul_dvd_mul_left π h7
      refine dvd_trans (pow_dvd_pow π (show t + 1 ≤ 2 * t by omega)) ?_
      rwa [show π * π ^ (2 * t - 1) = π ^ (2 * t) from by
        rw [← pow_succ']; congr 1; omega] at h8
    have h9 : π ^ (t + 1) ∣ π * (w * R.coeff 1) := by
      rw [hsub]
      exact dvd_sub hdvd1a h6
    have h10 : π * π ^ t ∣ π * (w * R.coeff 1) := by
      rwa [show π * π ^ t = π ^ (t + 1) from by rw [← pow_succ']]
    exact hpr.pow_dvd_of_dvd_mul_left _ hπw
      ((mul_dvd_mul_iff_left (hπ.ne_zero)).1 h10)
  -- the cofactor polygon: `(2t−1, 2)`-pure
  have hnpR0 : npHgt X R 0 = ((2 * t - 1 : ℕ) : ℕ∞) := by
    rw [npHgt_X]
    exact addVal_eq_of_pow_dvd_not_dvd hπ hr0dvd (by
      intro h6
      exact hr0not (by rwa [show 2 * t - 1 + 1 = 2 * t from by omega] at h6))
  have hnpR1 : ((t : ℕ) : ℕ∞) ≤ npHgt X R 1 := by
    rw [npHgt_X]
    exact (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hr1dvd
  have hnpR2 : npHgt X R 2 = ((0 : ℕ) : ℕ∞) := by
    rw [npHgt_X]
    have hc2 : R.coeff 2 = 1 := by
      have h6 := hRm.coeff_natDegree
      rwa [hRdeg] at h6
    rw [hc2]
    simp [(IsDiscreteValuationRing.addVal O).map_one]
  -- the three cleared values at slope data `(2t−1, 2)`
  have hcl0 : (2 : ℕ) • npHgt X R 0 + (((2 * t - 1) * 0 : ℕ) : ℕ∞)
      = ((2 * (2 * t - 1) : ℕ) : ℕ∞) := by
    rw [hnpR0, nsmul_eq_mul]
    push_cast
    ring
  have hcl2 : (2 : ℕ) • npHgt X R 2 + (((2 * t - 1) * 2 : ℕ) : ℕ∞)
      = ((2 * (2 * t - 1) : ℕ) : ℕ∞) := by
    rw [hnpR2, nsmul_eq_mul]
    push_cast
    ring
  have hcl1 : ((2 * (2 * t - 1) : ℕ) : ℕ∞)
      ≤ (2 : ℕ) • npHgt X R 1 + (((2 * t - 1) * 1 : ℕ) : ℕ∞) := by
    have hmono : (2 : ℕ) • ((t : ℕ) : ℕ∞) + (((2 * t - 1) * 1 : ℕ) : ℕ∞)
        ≤ (2 : ℕ) • npHgt X R 1 + (((2 * t - 1) * 1 : ℕ) : ℕ∞) := by
      gcongr
    refine le_trans ?_ hmono
    rw [nsmul_eq_mul]
    exact_mod_cast (by omega : (2 * (2 * t - 1) : ℕ) ≤ 2 * t + (2 * t - 1) * 1)
  have hsuppR : suppVal X R (2 * t - 1) 2 = ((2 * (2 * t - 1) : ℕ) : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · unfold suppVal
      exact le_trans (Finset.inf_le (show 0 ∈ Finset.range (R.natDegree + 1) by
        rw [hRdeg]; norm_num)) (le_of_eq hcl0)
    · unfold suppVal
      refine Finset.le_inf ?_
      intro j hj
      rw [hRdeg, Finset.mem_range] at hj
      interval_cases j
      · exact le_of_eq hcl0.symm
      · exact hcl1
      · exact le_of_eq hcl2.symm
  have hpureR : IsPure X R (2 * t - 1) 2 := by
    constructor
    · show (2 : ℕ) • npHgt X R 0 + (((2 * t - 1) * 0 : ℕ) : ℕ∞) = suppVal X R (2 * t - 1) 2
      rw [hcl0, hsuppR]
    · show (2 : ℕ) • npHgt X R (R.natDegree / (X : Polynomial O).natDegree)
        + (((2 * t - 1) * (R.natDegree / (X : Polynomial O).natDegree) : ℕ) : ℕ∞)
        = suppVal X R (2 * t - 1) 2
      rw [Polynomial.natDegree_X, hRdeg, Nat.div_one, hcl2, hsuppR]
  have hcop : Nat.Coprime (2 * t - 1) 2 :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).symm
  obtain ⟨hRirr, hRef⟩ := irreducible_of_isPure_natDegree_eq hπ hRm (by norm_num)
    hcop hpureR hRdeg
  -- assemble the type
  show typeOf (monicPoly a) = ramPairType
  have hdata : (typeOf (monicPoly a)).data = ({(2, 1), (2, 1)} : Multiset (ℕ × ℕ)) := by
    rw [typeOf_data, heqFR, monicFactors_mul hFm hRm,
      monicFactors_of_irreducible hFm hFirr, monicFactors_of_irreducible hRm hRirr,
      Multiset.map_add, Multiset.map_singleton, Multiset.map_singleton, hFef, hRef]
    rfl
  show typeOf (monicPoly a) = ⟨{(2, 1), (2, 1)}⟩
  rw [← hdata]

private theorem residue_eq_zero_of_dvd {π x : O} (hπ : Irreducible π)
    (h : π ∣ x) : IsLocalRing.residue O x = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hπ0 : IsLocalRing.residue O π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2
      ((IsLocalRing.mem_maximalIdeal π).2 (mem_nonunits_iff.2 hπ.not_isUnit))
  rw [map_mul, hπ0, zero_mul]

/-- ★ **The genre-(b) decision, ALL broken-polygon strata at once**: a class with
`v₁ = v` exact (`v ≥ 2`, `2v ≤ K`), `v₀ ≥ 2v`, `v₂ = 1`, `v₃ ≥ 1` is DECIDED
`{(1,1),(1,1),(2,1)}` — the cofactor's polygon breaks at abscissa 1 into two integral
width-1 faces, two linear factors. -/
theorem decidedAt_bBox {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) {v : ℕ}
    (hv : 2 ≤ v) (hvK : 2 * v ≤ K) {c : Coeff O 4 K} (hc : c ∈ bBox O K v) :
    DecidedAt O 4 splitTailType K c := by
  obtain ⟨h0, h1, h2, h3⟩ := hc
  intro a ha
  have hce2 : c ∈ e2Box O K := (mem_e2Box_iff c).2 ⟨by omega, by omega, h2, h3⟩
  obtain ⟨F, R, hFm, hRm, hFirr, hFef, hFdeg, hRdeg, heqFR, ⟨w, hw, hwne⟩, hf1⟩ :=
    e2_peel hK hπ hce2 ha
  obtain ⟨u1, hu1⟩ := hf1
  obtain ⟨hid0, hid1, hid2, hid3⟩ := coeff_mul_quadratics hFm hRm hFdeg hRdeg
  have hπw : ¬ π ∣ w := not_dvd_of_residue_ne_zero hπ hwne
  have hpr : Prime π := prime_of_irr hπ
  -- the lift coefficient identities
  have hpc0 : (monicPoly a).coeff 0 = a 0 :=
    monicPoly_coeff_lt a (show (0 : ℕ) < 4 by norm_num)
  have hpc1 : (monicPoly a).coeff 1 = a 1 :=
    monicPoly_coeff_lt a (show (1 : ℕ) < 4 by norm_num)
  have hA0 : a 0 = π * (w * R.coeff 0) := by
    have h := hid0
    rw [← heqFR, hpc0, hw] at h
    rw [h]; ring
  have hA1 : a 1 = π * (w * R.coeff 1) + π * (u1 * R.coeff 0) := by
    have h := hid1
    rw [← heqFR, hpc1, hw, hu1] at h
    rw [h]; ring
  -- exact valuation of `a 1`, lower bound on `a 0`
  have hexact1 : π ^ v ∣ a 1 ∧ ¬ π ^ (v + 1) ∣ a 1 := by
    have h := classCoeffVal_exact hπ ha (i := 1)
      (show classCoeffVal c 1 < K by show resOrd (c 1) < K; omega)
    rwa [show classCoeffVal c 1 = v from h1] at h
  have hdvd0a : π ^ (2 * v) ∣ a 0 := by
    refine (le_classCoeffVal_iff_dvd hπ (by omega) ha 0).1 ?_
    show 2 * v ≤ resOrd (c 0)
    exact h0
  -- the cofactor's constant coefficient: at least `π^(2v−1)`
  have hr0dvd : π ^ (2 * v - 1) ∣ R.coeff 0 := by
    have h6 : π ^ (2 * v) ∣ π * (w * R.coeff 0) := hA0 ▸ hdvd0a
    have h7 : π * π ^ (2 * v - 1) ∣ π * (w * R.coeff 0) := by
      rw [show π * π ^ (2 * v - 1) = π ^ (2 * v) from by
        rw [← pow_succ']; congr 1; omega]
      exact h6
    exact hpr.pow_dvd_of_dvd_mul_left _ hπw
      ((mul_dvd_mul_iff_left (hπ.ne_zero)).1 h7)
  -- the cofactor's middle coefficient: exactly `π^(v−1)`
  have hr1dvd : π ^ (v - 1) ∣ R.coeff 1 := by
    have hsub : π * (w * R.coeff 1) = a 1 - π * (u1 * R.coeff 0) := by
      rw [hA1]; ring
    have h6 : π ^ v ∣ π * (u1 * R.coeff 0) := by
      have h7 : π ^ (2 * v - 1) ∣ u1 * R.coeff 0 := Dvd.dvd.mul_left hr0dvd u1
      have h8 : π * π ^ (2 * v - 1) ∣ π * (u1 * R.coeff 0) := mul_dvd_mul_left π h7
      refine dvd_trans (pow_dvd_pow π (show v ≤ 2 * v by omega)) ?_
      rwa [show π * π ^ (2 * v - 1) = π ^ (2 * v) from by
        rw [← pow_succ']; congr 1; omega] at h8
    have h9 : π ^ v ∣ π * (w * R.coeff 1) := by
      rw [hsub]
      exact dvd_sub hexact1.1 h6
    have h10 : π * π ^ (v - 1) ∣ π * (w * R.coeff 1) := by
      rw [show π * π ^ (v - 1) = π ^ v from by rw [← pow_succ']; congr 1; omega]
      exact h9
    exact hpr.pow_dvd_of_dvd_mul_left _ hπw
      ((mul_dvd_mul_iff_left (hπ.ne_zero)).1 h10)
  have hr1not : ¬ π ^ v ∣ R.coeff 1 := by
    intro h6
    apply hexact1.2
    rw [hA1]
    refine dvd_add ?_ ?_
    · have h7 : π ^ v ∣ w * R.coeff 1 := Dvd.dvd.mul_left h6 w
      have h8 : π * π ^ v ∣ π * (w * R.coeff 1) := mul_dvd_mul_left π h7
      rwa [show π * π ^ v = π ^ (v + 1) from by rw [← pow_succ']] at h8
    · have h7 : π ^ (2 * v - 1) ∣ u1 * R.coeff 0 := Dvd.dvd.mul_left hr0dvd u1
      have h8 : π * π ^ (2 * v - 1) ∣ π * (u1 * R.coeff 0) := mul_dvd_mul_left π h7
      refine dvd_trans (pow_dvd_pow π (show v + 1 ≤ 2 * v by omega)) ?_
      rwa [show π * π ^ (2 * v - 1) = π ^ (2 * v) from by
        rw [← pow_succ']; congr 1; omega] at h8
  -- the cofactor reduces to `X²`
  have hRres : R.map (IsLocalRing.residue O) = X ^ R.natDegree := by
    rw [hRdeg]
    conv_lhs => rw [monic_quad_eq_coeffs hRm hRdeg]
    rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X]
    rw [residue_eq_zero_of_dvd hπ (dvd_trans (dvd_pow_self π (by omega : v - 1 ≠ 0)) hr1dvd),
      residue_eq_zero_of_dvd hπ (dvd_trans (dvd_pow_self π (by omega : 2 * v - 1 ≠ 0)) hr0dvd)]
    simp
  -- the cofactor's polygon values
  have hnpR0 : ((2 * v - 1 : ℕ) : ℕ∞) ≤ npHgt X R 0 := by
    rw [npHgt_X]
    exact (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hr0dvd
  have hnpR1 : npHgt X R 1 = ((v - 1 : ℕ) : ℕ∞) := by
    rw [npHgt_X]
    exact addVal_eq_of_pow_dvd_not_dvd hπ hr1dvd (by
      intro h6
      exact hr1not (by rwa [show v - 1 + 1 = v from by omega] at h6))
  have hnpR2 : npHgt X R 2 = ((0 : ℕ) : ℕ∞) := by
    rw [npHgt_X]
    have hc2 : R.coeff 2 = 1 := by
      have h6 := hRm.coeff_natDegree
      rwa [hRdeg] at h6
    rw [hc2]
    simp [(IsDiscreteValuationRing.addVal O).map_one]
  -- the `[1,2]` side at slope `v−1`
  have hcl1 : (1 : ℕ) • npHgt X R 1 + (((v - 1) * 1 : ℕ) : ℕ∞)
      = ((2 * (v - 1) : ℕ) : ℕ∞) := by
    rw [hnpR1, nsmul_eq_mul]
    push_cast
    ring
  have hcl2 : (1 : ℕ) • npHgt X R 2 + (((v - 1) * 2 : ℕ) : ℕ∞)
      = ((2 * (v - 1) : ℕ) : ℕ∞) := by
    rw [hnpR2, nsmul_eq_mul]
    push_cast
    ring
  have hcl0 : ((2 * (v - 1) : ℕ) : ℕ∞)
      ≤ (1 : ℕ) • npHgt X R 0 + (((v - 1) * 0 : ℕ) : ℕ∞) := by
    have hmono : (1 : ℕ) • ((2 * v - 1 : ℕ) : ℕ∞) + (((v - 1) * 0 : ℕ) : ℕ∞)
        ≤ (1 : ℕ) • npHgt X R 0 + (((v - 1) * 0 : ℕ) : ℕ∞) := by
      gcongr
    refine le_trans ?_ hmono
    rw [nsmul_eq_mul]
    exact_mod_cast (by omega : (2 * (v - 1) : ℕ) ≤ 1 * (2 * v - 1) + (v - 1) * 0)
  have hsuppR : suppVal X R (v - 1) 1 = ((2 * (v - 1) : ℕ) : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · unfold suppVal
      exact le_trans (Finset.inf_le (show 1 ∈ Finset.range (R.natDegree + 1) by
        rw [hRdeg]; norm_num)) (le_of_eq hcl1)
    · unfold suppVal
      refine Finset.le_inf ?_
      intro j hj
      rw [hRdeg, Finset.mem_range] at hj
      interval_cases j
      · exact hcl0
      · exact le_of_eq hcl1.symm
      · exact le_of_eq hcl2.symm
  have hO1R : OnSide X R (v - 1) 1 1 := by
    show (1 : ℕ) • npHgt X R 1 + (((v - 1) * 1 : ℕ) : ℕ∞) = suppVal X R (v - 1) 1
    rw [hcl1, hsuppR]
  have hO2R : OnSide X R (v - 1) 1 2 := by
    show (1 : ℕ) • npHgt X R 2 + (((v - 1) * 2 : ℕ) : ℕ∞) = suppVal X R (v - 1) 1
    rw [hcl2, hsuppR]
  have htopR : suppVal X R (v - 1) 1 ≠ ⊤ := by
    rw [hsuppR]
    exact ENat.coe_ne_top _
  -- the second peel: the `[1,2]` face splits off a linear
  obtain ⟨F', R'', hF'm, hR''m, hF'p, hF'dpos, heqR⟩ :=
    exists_pure_factor_of_two_point_side hπ hRm hRres (by omega : 0 < v - 1)
      (by norm_num) (Nat.coprime_one_right _) (show (1 : ℕ) < 2 by norm_num)
      (le_of_eq hRdeg.symm) hO1R hO2R htopR
  have hdegsum : F'.natDegree + R''.natDegree = 2 := by
    have h6 : R.natDegree = F'.natDegree + R''.natDegree := by
      rw [heqR]
      exact Polynomial.natDegree_mul hF'm.ne_zero hR''m.ne_zero
    omega
  have hF'deg : F'.natDegree = 1 := by
    rcases (by omega : F'.natDegree = 1 ∨ F'.natDegree = 2) with h12 | h12
    · exact h12
    exfalso
    have hR''deg0 : R''.natDegree = 0 := by omega
    have hR''1 : R'' = 1 := (Polynomial.Monic.natDegree_eq_zero hR''m).mp hR''deg0
    have hRF' : R = F' := by rw [heqR, hR''1, mul_one]
    have hO0 : OnSide X R (v - 1) 1 0 := by
      have h6 := hF'p.1
      rwa [← hRF'] at h6
    have h7 : (1 : ℕ) • npHgt X R 0 + (((v - 1) * 0 : ℕ) : ℕ∞)
        = ((2 * (v - 1) : ℕ) : ℕ∞) := by
      rw [show (1 : ℕ) • npHgt X R 0 + (((v - 1) * 0 : ℕ) : ℕ∞)
          = suppVal X R (v - 1) 1 from hO0, hsuppR]
    have h8 : npHgt X R 0 = ((2 * (v - 1) : ℕ) : ℕ∞) := by
      rw [one_nsmul] at h7
      simpa using h7
    rw [h8, Nat.cast_le] at hnpR0
    omega
  have hR''deg : R''.natDegree = 1 := by omega
  obtain ⟨hF'irr, hF'ef⟩ := irreducible_of_isPure_natDegree_eq hπ hF'm
    (by norm_num) (Nat.coprime_one_right _) hF'p hF'deg
  have hR''irr : Irreducible R'' := irreducible_of_monic_natDegree_one hR''m hR''deg
  have hR''ef : efPair R'' = (1, 1) := efPair_of_natDegree_one hR''m hR''deg
  -- assemble the type
  show typeOf (monicPoly a) = splitTailType
  have hdata : (typeOf (monicPoly a)).data
      = ({(1, 1), (1, 1), (2, 1)} : Multiset (ℕ × ℕ)) := by
    rw [typeOf_data, heqFR, heqR, monicFactors_mul hFm (hF'm.mul hR''m),
      monicFactors_mul hF'm hR''m, monicFactors_of_irreducible hFm hFirr,
      monicFactors_of_irreducible hF'm hF'irr,
      monicFactors_of_irreducible hR''m hR''irr,
      Multiset.map_add, Multiset.map_add, Multiset.map_singleton,
      Multiset.map_singleton, Multiset.map_singleton, hFef, hF'ef, hR''ef]
    decide
  show typeOf (monicPoly a) = ⟨{(1, 1), (1, 1), (2, 1)}⟩
  rw [← hdata]

/-- ★★ **The genre-(c) bank** — the width-2 integral-slope face, ALL corner depths at
once: every lift of a genre-(c) class factors as `F · R` with `F` the `(2,1)` block and
`R` `(s,1)`-pure; B.44's extraction `R = G.scaleRoots (π^s)` is `typeOf`-preserving and
its digit clause pins the reduction `Ḡ` to be EXACTLY the class-digit quadratic
`X² + (d₁/δ)·X + (d₀/δ) = X² + C (cPair π s c).1 · X + C (cPair π s c).2`. -/
private theorem e2_cGenre_bank {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {s : ℕ} (hs : 1 ≤ s) (hsK : 2 * s + 1 < K) {c : Coeff O 4 K}
    (h0 : resOrd (c 0) = 2 * s + 1) (h1 : s + 1 ≤ resOrd (c 1))
    (h2 : resOrd (c 2) = 1) (h3 : 1 ≤ resOrd (c 3))
    {a : Fin 4 → O} (ha : proj O 4 K a = c) :
    ∃ F R G : Polynomial O, F.Monic ∧ Irreducible F ∧ efPair F = (2, 1)
      ∧ R.Monic ∧ monicPoly a = F * R ∧ typeOf R = typeOf G
      ∧ G.Monic ∧ G.natDegree = 2
      ∧ G.map (IsLocalRing.residue O)
        = X ^ 2 + Polynomial.C (cPair π s c).1 * X + Polynomial.C (cPair π s c).2 := by
  have hce2 : c ∈ e2Box O K := (mem_e2Box_iff c).2 ⟨by omega, by omega, h2, h3⟩
  obtain ⟨F, R, hFm, hRm, hFirr, hFef, hFdeg, hRdeg, heqFR, ⟨w, hw, hwne⟩, hf1⟩ :=
    e2_peel hK hπ hce2 ha
  obtain ⟨u1, hu1⟩ := hf1
  obtain ⟨hid0, hid1, hid2, hid3⟩ := coeff_mul_quadratics hFm hRm hFdeg hRdeg
  have hπw : ¬ π ∣ w := not_dvd_of_residue_ne_zero hπ hwne
  have hpr : Prime π := prime_of_irr hπ
  -- the lift coefficient identities
  have hpc0 : (monicPoly a).coeff 0 = a 0 :=
    monicPoly_coeff_lt a (show (0 : ℕ) < 4 by norm_num)
  have hpc1 : (monicPoly a).coeff 1 = a 1 :=
    monicPoly_coeff_lt a (show (1 : ℕ) < 4 by norm_num)
  have hpc2 : (monicPoly a).coeff 2 = a 2 :=
    monicPoly_coeff_lt a (show (2 : ℕ) < 4 by norm_num)
  have hA0 : a 0 = π * (w * R.coeff 0) := by
    have h := hid0
    rw [← heqFR, hpc0, hw] at h
    rw [h]; ring
  have hA1 : a 1 = π * (w * R.coeff 1) + π * (u1 * R.coeff 0) := by
    have h := hid1
    rw [← heqFR, hpc1, hw, hu1] at h
    rw [h]; ring
  have hA2 : a 2 = π * w + π * (u1 * R.coeff 1) + R.coeff 0 := by
    have h := hid2
    rw [← heqFR, hpc2, hw, hu1] at h
    rw [h]; ring
  -- exact valuation of `a 0`, lower bound on `a 1`
  have hexact0 : π ^ (2 * s + 1) ∣ a 0 ∧ ¬ π ^ (2 * s + 1 + 1) ∣ a 0 := by
    have h := classCoeffVal_exact hπ ha (i := 0)
      (show classCoeffVal c 0 < K by show resOrd (c 0) < K; omega)
    rwa [show classCoeffVal c 0 = 2 * s + 1 from h0] at h
  have hdvd1a : π ^ (s + 1) ∣ a 1 := by
    refine (le_classCoeffVal_iff_dvd hπ (by omega) ha 1).1 ?_
    show s + 1 ≤ resOrd (c 1)
    exact h1
  -- the cofactor's constant coefficient: exactly `π^(2s)`
  have hr0dvd : π ^ (2 * s) ∣ R.coeff 0 := by
    have h6 : π ^ (2 * s + 1) ∣ π * (w * R.coeff 0) := hA0 ▸ hexact0.1
    have h7 : π * π ^ (2 * s) ∣ π * (w * R.coeff 0) := by
      rw [show π * π ^ (2 * s) = π ^ (2 * s + 1) from by rw [← pow_succ']]
      exact h6
    exact hpr.pow_dvd_of_dvd_mul_left _ hπw
      ((mul_dvd_mul_iff_left (hπ.ne_zero)).1 h7)
  have hr0not : ¬ π ^ (2 * s + 1) ∣ R.coeff 0 := by
    intro h6
    apply hexact0.2
    rw [hA0]
    have h7 : π ^ (2 * s + 1) ∣ w * R.coeff 0 := Dvd.dvd.mul_left h6 w
    have h8 : π * π ^ (2 * s + 1) ∣ π * (w * R.coeff 0) := mul_dvd_mul_left π h7
    rwa [show π * π ^ (2 * s + 1) = π ^ (2 * s + 1 + 1) from by rw [← pow_succ']] at h8
  -- the cofactor's middle coefficient: at least `π^s`
  have hr1dvd : π ^ s ∣ R.coeff 1 := by
    have hsub : π * (w * R.coeff 1) = a 1 - π * (u1 * R.coeff 0) := by
      rw [hA1]; ring
    have h6 : π ^ (s + 1) ∣ π * (u1 * R.coeff 0) := by
      have h7 : π ^ (2 * s) ∣ u1 * R.coeff 0 := Dvd.dvd.mul_left hr0dvd u1
      have h8 : π * π ^ (2 * s) ∣ π * (u1 * R.coeff 0) := mul_dvd_mul_left π h7
      refine dvd_trans (pow_dvd_pow π (show s + 1 ≤ 2 * s + 1 by omega)) ?_
      rwa [show π * π ^ (2 * s) = π ^ (2 * s + 1) from by rw [← pow_succ']] at h8
    have h9 : π ^ (s + 1) ∣ π * (w * R.coeff 1) := by
      rw [hsub]
      exact dvd_sub hdvd1a h6
    have h10 : π * π ^ s ∣ π * (w * R.coeff 1) := by
      rw [show π * π ^ s = π ^ (s + 1) from by rw [← pow_succ']]
      exact h9
    exact hpr.pow_dvd_of_dvd_mul_left _ hπw
      ((mul_dvd_mul_iff_left (hπ.ne_zero)).1 h10)
  -- the cofactor's polygon: `(s,1)`-pure
  have hnpR0 : npHgt X R 0 = ((2 * s : ℕ) : ℕ∞) := by
    rw [npHgt_X]
    exact addVal_eq_of_pow_dvd_not_dvd hπ hr0dvd hr0not
  have hnpR1 : ((s : ℕ) : ℕ∞) ≤ npHgt X R 1 := by
    rw [npHgt_X]
    exact (Uniformity.Hensel.pow_dvd_iff_le_addVal hπ).1 hr1dvd
  have hnpR2 : npHgt X R 2 = ((0 : ℕ) : ℕ∞) := by
    rw [npHgt_X]
    have hc2 : R.coeff 2 = 1 := by
      have h6 := hRm.coeff_natDegree
      rwa [hRdeg] at h6
    rw [hc2]
    simp [(IsDiscreteValuationRing.addVal O).map_one]
  have hcl0 : (1 : ℕ) • npHgt X R 0 + ((s * 0 : ℕ) : ℕ∞) = ((2 * s : ℕ) : ℕ∞) := by
    rw [hnpR0, nsmul_eq_mul]
    push_cast
    ring
  have hcl2 : (1 : ℕ) • npHgt X R 2 + ((s * 2 : ℕ) : ℕ∞) = ((2 * s : ℕ) : ℕ∞) := by
    rw [hnpR2, nsmul_eq_mul]
    push_cast
    ring
  have hcl1 : ((2 * s : ℕ) : ℕ∞) ≤ (1 : ℕ) • npHgt X R 1 + ((s * 1 : ℕ) : ℕ∞) := by
    have hmono : (1 : ℕ) • ((s : ℕ) : ℕ∞) + ((s * 1 : ℕ) : ℕ∞)
        ≤ (1 : ℕ) • npHgt X R 1 + ((s * 1 : ℕ) : ℕ∞) := by
      gcongr
    refine le_trans ?_ hmono
    rw [nsmul_eq_mul]
    exact_mod_cast (by omega : (2 * s : ℕ) ≤ 1 * s + s * 1)
  have hsuppR : suppVal X R s 1 = ((2 * s : ℕ) : ℕ∞) := by
    refine le_antisymm ?_ ?_
    · unfold suppVal
      exact le_trans (Finset.inf_le (show 0 ∈ Finset.range (R.natDegree + 1) by
        rw [hRdeg]; norm_num)) (le_of_eq hcl0)
    · unfold suppVal
      refine Finset.le_inf ?_
      intro j hj
      rw [hRdeg, Finset.mem_range] at hj
      interval_cases j
      · exact le_of_eq hcl0.symm
      · exact hcl1
      · exact le_of_eq hcl2.symm
  have hpureR : IsPure X R s 1 := by
    constructor
    · show (1 : ℕ) • npHgt X R 0 + ((s * 0 : ℕ) : ℕ∞) = suppVal X R s 1
      rw [hcl0, hsuppR]
    · show (1 : ℕ) • npHgt X R (R.natDegree / (X : Polynomial O).natDegree)
        + ((s * (R.natDegree / (X : Polynomial O).natDegree) : ℕ) : ℕ∞)
        = suppVal X R s 1
      rw [Polynomial.natDegree_X, hRdeg, Nat.div_one, hcl2, hsuppR]
  -- B.44's extraction: `R = G.scaleRoots (π^s)`, `typeOf`-preserving, digits pinned
  have hsuppR' : suppVal X R s 1 = ((s * R.natDegree : ℕ) : ℕ∞) := by
    rw [hRdeg, hsuppR, show (s * 2 : ℕ) = 2 * s from by ring]
  obtain ⟨G, hGm, hGdeg, hscale, hGtype, hGdig⟩ :=
    exists_scaleRoots_of_pure_integral hπ hRm (by rw [hRdeg]; norm_num) hpureR hsuppR'
  have hGdeg2 : G.natDegree = 2 := by rw [hGdeg, hRdeg]
  -- the class digits transported to the lift
  have hdig : ∀ (i : Fin 4) (vv : ℕ), vv < K → resDig π vv (c i) = digAt π vv (a i) := by
    intro i vv hvv
    rw [← congrFun ha i]
    exact resDig_mk hπ hvv (a i)
  -- the witnesses
  obtain ⟨y, hy⟩ := hr0dvd
  obtain ⟨z, hz⟩ := hr1dvd
  -- `δ = res w`
  obtain ⟨E, hE1, hE2⟩ : ∃ E, 2 * s - 1 = E ∧ 2 * s = E + 1 := ⟨2 * s - 1, rfl, by omega⟩
  have hδ : resDig π 1 (c 2) = IsLocalRing.residue O w := by
    rw [hdig 2 1 (by omega)]
    have hy' : R.coeff 0 = π ^ (E + 1) * y := by rw [← hE2]; exact hy
    have hEq : a 2 = π ^ 1 * (w + u1 * (π ^ s * z) + π ^ E * y) := by
      rw [pow_one, hA2, hy', hz]
      ring
    have hz1 : IsLocalRing.residue O (π ^ E * y) = 0 :=
      residue_eq_zero_of_dvd hπ
        (dvd_mul_of_dvd_left (dvd_pow_self π (by omega : E ≠ 0)) y)
    have hz2 : IsLocalRing.residue O (π ^ s * z) = 0 :=
      residue_eq_zero_of_dvd hπ
        (dvd_mul_of_dvd_left (dvd_pow_self π (by omega : s ≠ 0)) z)
    rw [digAt_eq hπ hEq, map_add, map_add, map_mul, hz2, hz1]
    ring
  -- `d₀ = res w · res (G₀)`
  have hg0 : IsLocalRing.residue O (G.coeff 0) = digAt π (2 * s) (R.coeff 0) := by
    have h6 := hGdig 0
    rwa [hRdeg, show (s * (2 - 0) : ℕ) = 2 * s from by ring] at h6
  have hd0 : resDig π (2 * s + 1) (c 0)
      = IsLocalRing.residue O w * IsLocalRing.residue O (G.coeff 0) := by
    rw [hdig 0 (2 * s + 1) (by omega)]
    have hEq : a 0 = π ^ (2 * s + 1) * (w * y) := by
      rw [hA0, hy]; ring
    rw [digAt_eq hπ hEq, map_mul, hg0, digAt_eq hπ hy]
  -- `d₁ = res w · res (G₁)`
  have hg1 : IsLocalRing.residue O (G.coeff 1) = digAt π s (R.coeff 1) := by
    have h6 := hGdig 1
    rwa [hRdeg, show (s * (2 - 1) : ℕ) = s from by ring] at h6
  have hd1 : resDig π (s + 1) (c 1)
      = IsLocalRing.residue O w * IsLocalRing.residue O (G.coeff 1) := by
    rw [hdig 1 (s + 1) (by omega)]
    have hEq : a 1 = π ^ (s + 1) * (w * z + π ^ s * (u1 * y)) := by
      rw [hA1, hy, hz]; ring
    rw [digAt_eq hπ hEq, map_add, map_mul, map_mul, hg1, digAt_eq hπ hz]
    rw [residue_eq_zero_of_dvd hπ (dvd_pow_self π (by omega : s ≠ 0))]
    ring
  -- the reduction of `G` is the class-digit quadratic
  have hδne : resDig π 1 (c 2) ≠ 0 := by
    rw [hδ]
    exact hwne
  have hGc1 : IsLocalRing.residue O (G.coeff 1) = (cPair π s c).1 := by
    show _ = resDig π (s + 1) (c 1) / resDig π 1 (c 2)
    rw [eq_div_iff hδne, hδ, hd1]
    ring
  have hGc0 : IsLocalRing.residue O (G.coeff 0) = (cPair π s c).2 := by
    show _ = resDig π (2 * s + 1) (c 0) / resDig π 1 (c 2)
    rw [eq_div_iff hδne, hδ, hd0]
    ring
  have hGbar : G.map (IsLocalRing.residue O)
      = X ^ 2 + Polynomial.C (cPair π s c).1 * X + Polynomial.C (cPair π s c).2 := by
    have h6 := monic_quad_eq_coeffs (hGm.map (IsLocalRing.residue O))
      (by rw [hGm.natDegree_map]; exact hGdeg2)
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hGc1, hGc0] at h6
    exact h6
  exact ⟨F, R, G, hFm, hFirr, hFef, hRm, heqFR, hGtype, hGm, hGdeg2, hGbar⟩

/-- ★★ **The genre-(c) IRREDUCIBLE decision — THE ℓ = 1 INERT LEAF, UNCONDITIONAL** (the
B.44 + B.59/B.60-mechanism leaf: the residual quadratic irreducible forces the cofactor
inert `(1,2)`): DECIDED `{(1,2),(2,1)}` at every corner depth. -/
theorem decidedAt_cIrrBox {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) {s : ℕ}
    (hs : 1 ≤ s) (hsK : 2 * s + 1 < K) {c : Coeff O 4 K}
    (hc : c ∈ cBox π K s (irrPairs (ResidueField O))) :
    DecidedAt O 4 inertTailType K c := by
  obtain ⟨h0, h1, h2, h3, hp⟩ := hc
  intro a ha
  obtain ⟨F, R, G, hFm, hFirr, hFef, hRm, heqFR, hRG, hGm, hGdeg, hGbar⟩ :=
    e2_cGenre_bank hK hπ hs hsK h0 h1 h2 h3 ha
  have hGirr : Irreducible (G.map (IsLocalRing.residue O)) := by
    rw [hGbar]
    exact hp
  have hGt : typeOf G = ⟨{(1, 2)}⟩ := by
    have h6 := Uniformity.Density.typeOf_inert_of_irreducible_map hGm
      (by rw [hGdeg]; norm_num) hGirr
    rwa [hGdeg] at h6
  have hRdata : (monicFactors R).map efPair = ({(1, 2)} : Multiset (ℕ × ℕ)) := by
    rw [← typeOf_data, hRG, hGt]
  show typeOf (monicPoly a) = inertTailType
  have hdata : (typeOf (monicPoly a)).data = ({(1, 2), (2, 1)} : Multiset (ℕ × ℕ)) := by
    rw [typeOf_data, heqFR, monicFactors_mul hFm hRm,
      monicFactors_of_irreducible hFm hFirr, Multiset.map_add,
      Multiset.map_singleton, hFef, hRdata]
    decide
  show typeOf (monicPoly a) = ⟨{(1, 2), (2, 1)}⟩
  rw [← hdata]

/-- ★★ **The genre-(c) SPLIT decision** (Hensel on the two distinct residual roots):
DECIDED `{(1,1),(1,1),(2,1)}` at every corner depth. -/
theorem decidedAt_cSplitBox {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) {s : ℕ}
    (hs : 1 ≤ s) (hsK : 2 * s + 1 < K) {c : Coeff O 4 K}
    (hc : c ∈ cBox π K s (splitPairs (ResidueField O))) :
    DecidedAt O 4 splitTailType K c := by
  obtain ⟨h0, h1, h2, h3, hp⟩ := hc
  intro a ha
  obtain ⟨F, R, G, hFm, hFirr, hFef, hRm, heqFR, hRG, hGm, hGdeg, hGbar⟩ :=
    e2_cGenre_bank hK hπ hs hsK h0 h1 h2 h3 ha
  obtain ⟨-, z₁, z₂, hz, heqψ⟩ := hp
  have hGsplit : G.map (IsLocalRing.residue O)
      = (X - Polynomial.C z₁) * (X - Polynomial.C z₂) := by
    rw [hGbar]
    exact heqψ
  have hroot : (G.map (IsLocalRing.residue O)).IsRoot z₁ := by
    rw [hGsplit]
    simp [Polynomial.IsRoot]
  have hsimple : (G.map (IsLocalRing.residue O)).derivative.eval z₁ ≠ 0 := by
    rw [hGsplit]
    have h6 : ((X - Polynomial.C z₁) * (X - Polynomial.C z₂)
        : Polynomial (ResidueField O)).derivative.eval z₁ = z₁ - z₂ := by
      simp [Polynomial.derivative_mul]
    rw [h6]
    exact sub_ne_zero.2 hz
  obtain ⟨ρ, Q, hQm, hGfact, hρres, hQres⟩ :=
    Uniformity.Hensel.exists_linear_factorization hGm hroot hsimple
  have hQdeg : Q.natDegree = 1 := by
    have h6 : G.natDegree = 1 + Q.natDegree := by
      rw [hGfact]
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero ρ) hQm.ne_zero,
        Polynomial.natDegree_X_sub_C]
    omega
  obtain ⟨q0, hQform⟩ : ∃ q0, Q = X + Polynomial.C q0 := ⟨Q.coeff 0, hQm.eq_X_add_C hQdeg⟩
  have hGt : typeOf G = Uniformity.Density.splitType := by
    rw [hGfact, hQform, show (X + Polynomial.C q0 : Polynomial O)
        = X - Polynomial.C (-q0) from by rw [map_neg, sub_neg_eq_add]]
    exact typeOf_mul_linear ρ (-q0)
  have hRdata : (monicFactors R).map efPair = ({(1, 1), (1, 1)} : Multiset (ℕ × ℕ)) := by
    rw [← typeOf_data, hRG, hGt]
    rfl
  show typeOf (monicPoly a) = splitTailType
  have hdata : (typeOf (monicPoly a)).data
      = ({(1, 1), (1, 1), (2, 1)} : Multiset (ℕ × ℕ)) := by
    rw [typeOf_data, heqFR, monicFactors_mul hFm hRm,
      monicFactors_of_irreducible hFm hFirr, Multiset.map_add,
      Multiset.map_singleton, hFef, hRdata]
    decide
  show typeOf (monicPoly a) = ⟨{(1, 1), (1, 1), (2, 1)}⟩
  rw [← hdata]

end Decisions

/-! ## §4 — the σ-shape exclusion: only the three named types live on `e2Box` -/

section Shape

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

private theorem typeOf_eq_of_data {f : Polynomial O} {σ : FactorizationType}
    (h : (typeOf f).data = σ.data) : typeOf f = σ := by
  have h2 : (⟨(typeOf f).data⟩ : FactorizationType) = ⟨σ.data⟩ := by rw [h]
  exact h2

/-- ★ **The shape pin**: every lift of an `e2Box` class has type `{(2,1),(2,1)}`,
`{(1,1),(1,1),(2,1)}`, or `{(1,2),(2,1)}` — the `(2,1)` block is forced, and a monic
quadratic cofactor has only the three shapes. -/
theorem typeOf_e2_mem {K : ℕ} (hK : 3 ≤ K) {c : Coeff O 4 K} (hc : c ∈ e2Box O K)
    {a : Fin 4 → O} (ha : proj O 4 K a = c) :
    typeOf (monicPoly a) = ramPairType ∨ typeOf (monicPoly a) = splitTailType
      ∨ typeOf (monicPoly a) = inertTailType := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨F, R, hFm, hRm, hFirr, hFef, hRdeg, heqFR⟩ :=
    exists_ramQuad_factor_of_e2 hK hπ hc ha
  have hspec := monicFactors_spec hRm
  have hdegs : R.natDegree = ((monicFactors R).map Polynomial.natDegree).sum := by
    conv_lhs => rw [← hspec.2]
    exact Polynomial.natDegree_multiset_prod_of_monic _ (fun p hp => (hspec.1 p hp).1)
  obtain ⟨g, hg⟩ := exists_mem_monicFactors hRm (by omega)
  have hgm := (hspec.1 g hg).1
  have hgpos : 0 < g.natDegree := natDegree_pos_of_mem_monicFactors hRm hg
  obtain ⟨T, hT⟩ := Multiset.exists_cons_of_mem hg
  have hsum : g.natDegree + (T.map Polynomial.natDegree).sum = 2 := by
    have h4 := hdegs
    rw [hT, Multiset.map_cons, Multiset.sum_cons, hRdeg] at h4
    omega
  have hdata0 : (typeOf (monicPoly a)).data
      = ({(2, 1)} : Multiset (ℕ × ℕ)) + (monicFactors R).map efPair := by
    rw [typeOf_data, heqFR, monicFactors_mul hFm hRm,
      monicFactors_of_irreducible hFm hFirr, Multiset.map_add,
      Multiset.map_singleton, hFef]
  rcases (by omega : g.natDegree = 2 ∨ g.natDegree = 1) with hd2 | hd1
  · -- one quadratic factor: `(2,1)` or `(1,2)`
    have hTzero : T = 0 := by
      by_contra hne
      obtain ⟨g', hg'⟩ := Multiset.exists_mem_of_ne_zero hne
      have h5 : 1 ≤ g'.natDegree := natDegree_pos_of_mem_monicFactors hRm
        (by rw [hT]; exact Multiset.mem_cons_of_mem hg')
      have h6 : g'.natDegree ≤ (T.map Polynomial.natDegree).sum :=
        Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
          (Multiset.mem_map_of_mem _ hg')
      omega
    have hfR : monicFactors R = {g} := by
      rw [hT, hTzero]
      exact Multiset.cons_zero g
    have hef : ramIndexOf g * inertiaDegOf g = 2 := by
      rw [ramIndexOf_mul_inertiaDegOf hgm hgpos, hd2]
    have hinpos : 0 < inertiaDegOf g := inertiaDegOf_pos (normValues_nonempty hgm hgpos)
    have hrpos : 0 < ramIndexOf g := by
      rcases Nat.eq_zero_or_pos (ramIndexOf g) with h5 | h5
      · rw [h5, zero_mul] at hef
        omega
      · exact h5
    have hrle : ramIndexOf g ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨inertiaDegOf g, hef.symm⟩
    rcases (by omega : ramIndexOf g = 1 ∨ ramIndexOf g = 2) with h5 | h5
    · -- `(1,2)`: the inert tail
      right; right
      refine typeOf_eq_of_data ?_
      rw [hdata0, hfR, Multiset.map_singleton]
      have h6 : efPair g = (1, 2) := by
        unfold efPair
        rw [h5]
        rw [h5, one_mul] at hef
        rw [hef]
      rw [h6]
      decide
    · -- `(2,1)`: the ram pair
      left
      refine typeOf_eq_of_data ?_
      rw [hdata0, hfR, Multiset.map_singleton]
      have h6 : efPair g = (2, 1) := by
        unfold efPair
        rw [h5]
        rw [h5] at hef
        rw [show inertiaDegOf g = 1 from by omega]
      rw [h6]
      decide
  · -- two linear factors: the split tail
    have hTsum : (T.map Polynomial.natDegree).sum = 1 := by omega
    have hTne : T ≠ 0 := by
      intro h5
      rw [h5] at hTsum
      simp at hTsum
    obtain ⟨g₂, hg₂⟩ := Multiset.exists_mem_of_ne_zero hTne
    have hg₂mem : g₂ ∈ monicFactors R := by
      rw [hT]
      exact Multiset.mem_cons_of_mem hg₂
    have hg₂m := (hspec.1 g₂ hg₂mem).1
    obtain ⟨T', hT'⟩ := Multiset.exists_cons_of_mem hg₂
    have hsum2 : g₂.natDegree + (T'.map Polynomial.natDegree).sum = 1 := by
      have h6 := hTsum
      rw [hT', Multiset.map_cons, Multiset.sum_cons] at h6
      omega
    have hg₂pos : 1 ≤ g₂.natDegree := natDegree_pos_of_mem_monicFactors hRm hg₂mem
    have hg₂deg : g₂.natDegree = 1 := by omega
    have hT'zero : T' = 0 := by
      by_contra hne
      obtain ⟨g₃, hg₃⟩ := Multiset.exists_mem_of_ne_zero hne
      have h5 : 1 ≤ g₃.natDegree := natDegree_pos_of_mem_monicFactors hRm
        (by rw [hT, hT']
            exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hg₃))
      have h6 : g₃.natDegree ≤ (T'.map Polynomial.natDegree).sum :=
        Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
          (Multiset.mem_map_of_mem _ hg₃)
      omega
    have hfR : monicFactors R = {g, g₂} := by
      rw [hT, hT', hT'zero, Multiset.cons_zero]
      rfl
    right; left
    refine typeOf_eq_of_data ?_
    rw [hdata0, hfR, show ({g, g₂} : Multiset (Polynomial O)).map efPair
        = {efPair g, efPair g₂} from by
      rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
      rfl]
    rw [efPair_of_natDegree_one hgm hd1, efPair_of_natDegree_one hg₂m hg₂deg]
    decide

/-- Every OTHER type has an EMPTY decided set on `e2Box` — the `∀ σ` closure engine
(strengthens IFCG34's `not_decidedAt_e2_of_singleton` to all off-shape types). -/
theorem decided_inter_e2_eq_empty_of_shape {K : ℕ} (hK : 3 ≤ K)
    {σ : FactorizationType} (h1 : σ ≠ ramPairType) (h2 : σ ≠ splitTailType)
    (h3 : σ ≠ inertTailType) :
    decidedSet O 4 σ K ∩ e2Box O K = (∅ : Set (Coeff O 4 K)) := by
  ext c
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hdec, hc⟩
  obtain ⟨a, ha⟩ := proj_surjective O 4 K c
  have htype := hdec a ha
  rcases typeOf_e2_mem hK hc ha with h | h | h
  · exact h1 (htype ▸ h)
  · exact h2 (htype ▸ h)
  · exact h3 (htype ▸ h)

end Shape

/-! ## §5 — the depth-0 partition of `e2Box` and the decided-set identities -/

section Partition

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

private theorem ne_of_data_ne {σ τ : FactorizationType} (h : σ.data ≠ τ.data) :
    σ ≠ τ := fun he => h (by rw [he])

private theorem ramPair_ne_splitTail : ramPairType ≠ splitTailType :=
  ne_of_data_ne (by decide)

private theorem ramPair_ne_inertTail : ramPairType ≠ inertTailType :=
  ne_of_data_ne (by decide)

private theorem splitTail_ne_inertTail : splitTailType ≠ inertTailType :=
  ne_of_data_ne (by decide)

/-- The stratum index Finsets (visibility windows). -/
def Ta (K : ℕ) : Finset ℕ := (Finset.range K).filter (fun t => 2 ≤ t ∧ 2 * t < K)

def Vb (K : ℕ) : Finset ℕ := (Finset.range K).filter (fun v => 2 ≤ v ∧ 2 * v ≤ K)

def Sc (K : ℕ) : Finset ℕ :=
  (Finset.range K).filter (fun s => 1 ≤ s ∧ 2 * s + 1 < K)

theorem mem_Ta {K t : ℕ} : t ∈ Ta K ↔ 2 ≤ t ∧ 2 * t < K := by
  unfold Ta
  rw [Finset.mem_filter, Finset.mem_range]
  omega

theorem mem_Vb {K v : ℕ} : v ∈ Vb K ↔ 2 ≤ v ∧ 2 * v ≤ K := by
  unfold Vb
  rw [Finset.mem_filter, Finset.mem_range]
  omega

theorem mem_Sc {K s : ℕ} : s ∈ Sc K ↔ 1 ≤ s ∧ 2 * s + 1 < K := by
  unfold Sc
  rw [Finset.mem_filter, Finset.mem_range]
  omega

/-- The dd carrier, re-read through `Sc`. -/
theorem e2DdBox_eq (π : O) (K : ℕ) :
    e2DdBox π K = ⋃ s ∈ Sc K, cBox π K s (ddPairs (ResidueField O)) := rfl

-- subset facts
private theorem aBox_subset_e2Box {K t : ℕ} (ht : 2 ≤ t) :
    aBox O K t ⊆ e2Box O K := by
  rintro c ⟨h0, h1, h2, h3⟩
  exact (mem_e2Box_iff c).2 ⟨by omega, by omega, h2, h3⟩

private theorem bBox_subset_e2Box {K v : ℕ} (hv : 2 ≤ v) :
    bBox O K v ⊆ e2Box O K := by
  rintro c ⟨h0, h1, h2, h3⟩
  exact (mem_e2Box_iff c).2 ⟨by omega, by omega, h2, h3⟩

private theorem cBox_subset_e2Box {π : O} {K s : ℕ} (hs : 1 ≤ s)
    {P : Set (ResidueField O × ResidueField O)} :
    cBox π K s P ⊆ e2Box O K := by
  rintro c ⟨h0, h1, h2, h3, -⟩
  exact (mem_e2Box_iff c).2 ⟨by omega, by omega, h2, h3⟩

private theorem bdBox_subset_e2Box {K : ℕ} (hK : 3 ≤ K) :
    bdBox O K ⊆ e2Box O K := by
  rintro c ⟨h0, h1, h2, h3⟩
  exact (mem_e2Box_iff c).2 ⟨by omega, by omega, h2, h3⟩

/-- ★ **The genre exhaustion**: every `e2Box` class is in a visible genre box or the
boundary cell. -/
theorem mem_genre_cases {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π)
    {c : Coeff O 4 K} (hc : c ∈ e2Box O K) :
    (∃ t ∈ Ta K, c ∈ aBox O K t)
      ∨ (∃ v ∈ Vb K, c ∈ bBox O K v)
      ∨ (∃ s ∈ Sc K, c ∈ cBox π K s (splitPairs (ResidueField O)))
      ∨ (∃ s ∈ Sc K, c ∈ cBox π K s (irrPairs (ResidueField O)))
      ∨ c ∈ e2DdBox π K
      ∨ c ∈ bdBox O K := by
  obtain ⟨h0, h1, h2, h3⟩ := (mem_e2Box_iff c).1 hc
  have h0K : resOrd (c 0) ≤ K := classCoeffVal_le c 0
  have h1K : resOrd (c 1) ≤ K := classCoeffVal_le c 1
  by_cases hb : 2 * resOrd (c 1) ≤ resOrd (c 0)
  · -- genre (b)
    refine Or.inr (Or.inl ⟨resOrd (c 1), mem_Vb.2 ⟨by omega, by omega⟩,
      ⟨hb, rfl, h2, h3⟩⟩)
  push Not at hb
  by_cases hbd : resOrd (c 0) = K
  · -- the boundary
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega, h2, h3⟩))))
  have h0lt : resOrd (c 0) < K := by omega
  rcases Nat.even_or_odd (resOrd (c 0)) with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- genre (a): the corner is even
    refine Or.inl ⟨r, mem_Ta.2 ⟨by omega, by omega⟩, ⟨by omega, by omega, h2, h3⟩⟩
  · -- genre (c): the corner is odd — the residual trichotomy
    have hs1 : 1 ≤ r := by omega
    have hsK : 2 * r + 1 < K := by omega
    have hd0ne : resDig π (2 * r + 1) (c 0) ≠ 0 := by
      have h5 := (resOrd_eq_iff_resDig hπ (v := 2 * r + 1) (by omega) (c 0)).1 (by omega)
      exact h5.2
    have hδne : resDig π 1 (c 2) ≠ 0 := by
      have h5 := (resOrd_eq_iff_resDig hπ (v := 1) (by omega) (c 2)).1 h2
      exact h5.2
    have hsnd : (cPair π r c).2 ≠ 0 := by
      show resDig π (2 * r + 1) (c 0) / resDig π 1 (c 2) ≠ 0
      exact div_ne_zero hd0ne hδne
    have hmem : ∀ P : Set (ResidueField O × ResidueField O), cPair π r c ∈ P →
        c ∈ cBox π K r P := by
      intro P hP
      exact ⟨by omega, by omega, h2, h3, hP⟩
    rcases pair_trichotomy hsnd with hP | hP | hP
    · exact Or.inr (Or.inr (Or.inl ⟨r, mem_Sc.2 ⟨hs1, hsK⟩, hmem _ hP⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨r, mem_Sc.2 ⟨hs1, hsK⟩, hmem _ hP⟩)))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      rw [e2DdBox_eq]
      exact Set.mem_biUnion (mem_Sc.2 ⟨hs1, hsK⟩) (hmem _ hP)

private theorem e2DdBox_subset_e2Box {π : O} {K : ℕ} :
    e2DdBox π K ⊆ e2Box O K := by
  rw [e2DdBox_eq]
  exact Set.iUnion₂_subset fun s hs => cBox_subset_e2Box (mem_Sc.1 hs).1

/-- ★ **The ramPair identity**: the σ = `{(2,1),(2,1)}` decided slice of `e2Box` is the
visible genre-(a) union plus the (kept) dd and boundary terms. -/
theorem decided_ramPair_inter_e2Box {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    decidedSet O 4 ramPairType K ∩ e2Box O K
      = (⋃ t ∈ Ta K, aBox O K t)
        ∪ ((decidedSet O 4 ramPairType K ∩ e2DdBox π K)
          ∪ (decidedSet O 4 ramPairType K ∩ bdBox O K)) := by
  ext c
  constructor
  · rintro ⟨hdec, hc⟩
    rcases mem_genre_cases hK hπ hc with ⟨t, ht, hA⟩ | ⟨v, hv, hB⟩ | ⟨s, hs, hC⟩
      | ⟨s, hs, hC⟩ | hD | hBd
    · exact Or.inl (Set.mem_biUnion ht hA)
    · exact absurd (decidedAt_unique hdec
        (decidedAt_bBox hK hπ (mem_Vb.1 hv).1 (mem_Vb.1 hv).2 hB)) ramPair_ne_splitTail
    · exact absurd (decidedAt_unique hdec
        (decidedAt_cSplitBox hK hπ (mem_Sc.1 hs).1 (mem_Sc.1 hs).2 hC))
        ramPair_ne_splitTail
    · exact absurd (decidedAt_unique hdec
        (decidedAt_cIrrBox hK hπ (mem_Sc.1 hs).1 (mem_Sc.1 hs).2 hC))
        ramPair_ne_inertTail
    · exact Or.inr (Or.inl ⟨hdec, hD⟩)
    · exact Or.inr (Or.inr ⟨hdec, hBd⟩)
  · rintro (hA | ⟨hdec, hD⟩ | ⟨hdec, hBd⟩)
    · obtain ⟨t, ht, hA'⟩ := Set.mem_iUnion₂.1 hA
      exact ⟨decidedAt_aBox hK hπ (mem_Ta.1 ht).1 (mem_Ta.1 ht).2 hA',
        aBox_subset_e2Box (mem_Ta.1 ht).1 hA'⟩
    · exact ⟨hdec, e2DdBox_subset_e2Box hD⟩
    · exact ⟨hdec, bdBox_subset_e2Box hK hBd⟩

/-- ★ **The splitTail identity**: genre (b) plus genre (c)-split plus the kept terms. -/
theorem decided_splitTail_inter_e2Box {K : ℕ} (hK : 3 ≤ K) {π : O}
    (hπ : Irreducible π) :
    decidedSet O 4 splitTailType K ∩ e2Box O K
      = ((⋃ v ∈ Vb K, bBox O K v)
          ∪ ⋃ s ∈ Sc K, cBox π K s (splitPairs (ResidueField O)))
        ∪ ((decidedSet O 4 splitTailType K ∩ e2DdBox π K)
          ∪ (decidedSet O 4 splitTailType K ∩ bdBox O K)) := by
  ext c
  constructor
  · rintro ⟨hdec, hc⟩
    rcases mem_genre_cases hK hπ hc with ⟨t, ht, hA⟩ | ⟨v, hv, hB⟩ | ⟨s, hs, hC⟩
      | ⟨s, hs, hC⟩ | hD | hBd
    · exact absurd (decidedAt_unique hdec
        (decidedAt_aBox hK hπ (mem_Ta.1 ht).1 (mem_Ta.1 ht).2 hA))
        ramPair_ne_splitTail.symm
    · exact Or.inl (Or.inl (Set.mem_biUnion hv hB))
    · exact Or.inl (Or.inr (Set.mem_biUnion hs hC))
    · exact absurd (decidedAt_unique hdec
        (decidedAt_cIrrBox hK hπ (mem_Sc.1 hs).1 (mem_Sc.1 hs).2 hC))
        splitTail_ne_inertTail
    · exact Or.inr (Or.inl ⟨hdec, hD⟩)
    · exact Or.inr (Or.inr ⟨hdec, hBd⟩)
  · rintro ((hB | hC) | ⟨hdec, hD⟩ | ⟨hdec, hBd⟩)
    · obtain ⟨v, hv, hB'⟩ := Set.mem_iUnion₂.1 hB
      exact ⟨decidedAt_bBox hK hπ (mem_Vb.1 hv).1 (mem_Vb.1 hv).2 hB',
        bBox_subset_e2Box (mem_Vb.1 hv).1 hB'⟩
    · obtain ⟨s, hs, hC'⟩ := Set.mem_iUnion₂.1 hC
      exact ⟨decidedAt_cSplitBox hK hπ (mem_Sc.1 hs).1 (mem_Sc.1 hs).2 hC',
        cBox_subset_e2Box (mem_Sc.1 hs).1 hC'⟩
    · exact ⟨hdec, e2DdBox_subset_e2Box hD⟩
    · exact ⟨hdec, bdBox_subset_e2Box hK hBd⟩

/-- ★ **The inertTail identity**: genre (c)-irreducible plus the kept terms. -/
theorem decided_inertTail_inter_e2Box {K : ℕ} (hK : 3 ≤ K) {π : O}
    (hπ : Irreducible π) :
    decidedSet O 4 inertTailType K ∩ e2Box O K
      = (⋃ s ∈ Sc K, cBox π K s (irrPairs (ResidueField O)))
        ∪ ((decidedSet O 4 inertTailType K ∩ e2DdBox π K)
          ∪ (decidedSet O 4 inertTailType K ∩ bdBox O K)) := by
  ext c
  constructor
  · rintro ⟨hdec, hc⟩
    rcases mem_genre_cases hK hπ hc with ⟨t, ht, hA⟩ | ⟨v, hv, hB⟩ | ⟨s, hs, hC⟩
      | ⟨s, hs, hC⟩ | hD | hBd
    · exact absurd (decidedAt_unique hdec
        (decidedAt_aBox hK hπ (mem_Ta.1 ht).1 (mem_Ta.1 ht).2 hA))
        ramPair_ne_inertTail.symm
    · exact absurd (decidedAt_unique hdec
        (decidedAt_bBox hK hπ (mem_Vb.1 hv).1 (mem_Vb.1 hv).2 hB))
        splitTail_ne_inertTail.symm
    · exact absurd (decidedAt_unique hdec
        (decidedAt_cSplitBox hK hπ (mem_Sc.1 hs).1 (mem_Sc.1 hs).2 hC))
        splitTail_ne_inertTail.symm
    · exact Or.inl (Set.mem_biUnion hs hC)
    · exact Or.inr (Or.inl ⟨hdec, hD⟩)
    · exact Or.inr (Or.inr ⟨hdec, hBd⟩)
  · rintro (hC | ⟨hdec, hD⟩ | ⟨hdec, hBd⟩)
    · obtain ⟨s, hs, hC'⟩ := Set.mem_iUnion₂.1 hC
      exact ⟨decidedAt_cIrrBox hK hπ (mem_Sc.1 hs).1 (mem_Sc.1 hs).2 hC',
        cBox_subset_e2Box (mem_Sc.1 hs).1 hC'⟩
    · exact ⟨hdec, e2DdBox_subset_e2Box hD⟩
    · exact ⟨hdec, bdBox_subset_e2Box hK hBd⟩

end Partition

/-! ## §6 — the exact level-`K` counts -/

section Counts

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

-- IFCG51's private biUnion counter, reproduced (the sanctioned replay).
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
        simp [Finset.mem_cons, or_and_right, Set.mem_iUnion]
      have hd : Disjoint (f a) (⋃ i ∈ s, f i) := by
        rw [Set.disjoint_right]
        intro x hx hxa
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
        exact (Set.disjoint_left.1 (hdisj a (Finset.mem_cons_self a s) i
          (Finset.mem_cons_of_mem hi) (by rintro rfl; exact ha hi))) hxa hxi
      rw [hcons, Set.ncard_union_eq hd, Finset.sum_cons,
        ih (fun i hi j hj hij => hdisj i (Finset.mem_cons_of_mem hi) j
          (Finset.mem_cons_of_mem hj) hij)]

-- pairwise stratum disjointness
private theorem aBox_pairwise {K : ℕ} : ∀ t ∈ Ta K, ∀ t' ∈ Ta K, t ≠ t' →
    Disjoint (aBox O K t) (aBox O K t') := by
  intro t _ t' _ hne
  rw [Set.disjoint_left]
  rintro c ⟨h0, -, -, -⟩ ⟨h0', -, -, -⟩
  exact hne (by omega)

private theorem bBox_pairwise {K : ℕ} : ∀ v ∈ Vb K, ∀ v' ∈ Vb K, v ≠ v' →
    Disjoint (bBox O K v) (bBox O K v') := by
  intro v _ v' _ hne
  rw [Set.disjoint_left]
  rintro c ⟨-, h1, -, -⟩ ⟨-, h1', -, -⟩
  exact hne (by omega)

private theorem cBox_pairwise {π : O} {K : ℕ}
    {P P' : Set (ResidueField O × ResidueField O)} :
    ∀ s ∈ Sc K, ∀ s' ∈ Sc K, s ≠ s' → Disjoint (cBox π K s P) (cBox π K s' P') := by
  intro s _ s' _ hne
  rw [Set.disjoint_left]
  rintro c ⟨h0, -, -, -, -⟩ ⟨h0', -, -, -, -⟩
  exact hne (by omega)

/-- ★★ **The ramPair count**: exact at every level. -/
theorem card_decided_ramPair {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    Nat.card ((decidedSet O 4 ramPairType K ∩ e2Box O K) : Set (Coeff O 4 K))
      = (∑ t ∈ Ta K, Nat.card (aBox O K t : Set (Coeff O 4 K)))
        + (Nat.card ((decidedSet O 4 ramPairType K ∩ e2DdBox π K) : Set (Coeff O 4 K))
          + Nat.card ((decidedSet O 4 ramPairType K ∩ bdBox O K) : Set (Coeff O 4 K))) := by
  have hd2 : Disjoint (decidedSet O 4 ramPairType K ∩ e2DdBox π K)
      (decidedSet O 4 ramPairType K ∩ bdBox O K) := by
    rw [Set.disjoint_left]
    rintro c ⟨-, hD⟩ ⟨-, hBd⟩
    rw [e2DdBox_eq] at hD
    obtain ⟨s, hs, hC⟩ := Set.mem_iUnion₂.1 hD
    obtain ⟨h0, -, -, -, -⟩ := hC
    obtain ⟨h0', -, -, -⟩ := hBd
    have := (mem_Sc.1 hs).2
    omega
  have hd1 : Disjoint (⋃ t ∈ Ta K, aBox O K t)
      ((decidedSet O 4 ramPairType K ∩ e2DdBox π K)
        ∪ (decidedSet O 4 ramPairType K ∩ bdBox O K)) := by
    rw [Set.disjoint_left]
    intro c hcA hcX
    obtain ⟨t, ht, hA⟩ := Set.mem_iUnion₂.1 hcA
    obtain ⟨h0, -, -, -⟩ := hA
    rcases hcX with ⟨-, hD⟩ | ⟨-, hBd⟩
    · rw [e2DdBox_eq] at hD
      obtain ⟨s, hs, hC⟩ := Set.mem_iUnion₂.1 hD
      obtain ⟨h0', -, -, -, -⟩ := hC
      omega
    · obtain ⟨h0', -, -, -⟩ := hBd
      have := (mem_Ta.1 ht).2
      omega
  rw [decided_ramPair_inter_e2Box hK hπ]
  simp only [Nat.card_coe_set_eq]
  rw [Set.ncard_union_eq hd1, Set.ncard_union_eq hd2, ncard_biUnion_eq _ _ aBox_pairwise]

/-- ★★ **The splitTail count**: exact at every level. -/
theorem card_decided_splitTail {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    Nat.card ((decidedSet O 4 splitTailType K ∩ e2Box O K) : Set (Coeff O 4 K))
      = ((∑ v ∈ Vb K, Nat.card (bBox O K v : Set (Coeff O 4 K)))
          + ∑ s ∈ Sc K, Nat.card ((cBox π K s (splitPairs (ResidueField O)))
              : Set (Coeff O 4 K)))
        + (Nat.card ((decidedSet O 4 splitTailType K ∩ e2DdBox π K) : Set (Coeff O 4 K))
          + Nat.card ((decidedSet O 4 splitTailType K ∩ bdBox O K) : Set (Coeff O 4 K))) := by
  have hd2 : Disjoint (decidedSet O 4 splitTailType K ∩ e2DdBox π K)
      (decidedSet O 4 splitTailType K ∩ bdBox O K) := by
    rw [Set.disjoint_left]
    rintro c ⟨-, hD⟩ ⟨-, hBd⟩
    rw [e2DdBox_eq] at hD
    obtain ⟨s, hs, hC⟩ := Set.mem_iUnion₂.1 hD
    obtain ⟨h0, -, -, -, -⟩ := hC
    obtain ⟨h0', -, -, -⟩ := hBd
    have := (mem_Sc.1 hs).2
    omega
  have hdBC : Disjoint (⋃ v ∈ Vb K, bBox O K v)
      (⋃ s ∈ Sc K, cBox π K s (splitPairs (ResidueField O))) := by
    rw [Set.disjoint_left]
    intro c hcB hcC
    obtain ⟨v, hv, hB⟩ := Set.mem_iUnion₂.1 hcB
    obtain ⟨s, hs, hC⟩ := Set.mem_iUnion₂.1 hcC
    obtain ⟨h0, h1, -, -⟩ := hB
    obtain ⟨h0', h1', -, -, -⟩ := hC
    omega
  have hd1 : Disjoint ((⋃ v ∈ Vb K, bBox O K v)
      ∪ ⋃ s ∈ Sc K, cBox π K s (splitPairs (ResidueField O)))
      ((decidedSet O 4 splitTailType K ∩ e2DdBox π K)
        ∪ (decidedSet O 4 splitTailType K ∩ bdBox O K)) := by
    rw [Set.disjoint_left]
    intro c hcBC hcX
    have hX : (∃ s ∈ Sc K, c ∈ cBox π K s (ddPairs (ResidueField O))) ∨ c ∈ bdBox O K := by
      rcases hcX with ⟨-, hD⟩ | ⟨-, hBd⟩
      · rw [e2DdBox_eq] at hD
        obtain ⟨s, hs, hC⟩ := Set.mem_iUnion₂.1 hD
        exact Or.inl ⟨s, hs, hC⟩
      · exact Or.inr hBd
    rcases hcBC with hcB | hcC
    · obtain ⟨v, hv, hB⟩ := Set.mem_iUnion₂.1 hcB
      obtain ⟨h0, h1, -, -⟩ := hB
      have hvV := (mem_Vb.1 hv)
      rcases hX with ⟨s, hs, hC⟩ | hBd
      · obtain ⟨h0', h1', -, -, -⟩ := hC
        omega
      · obtain ⟨h0', h1', -, -⟩ := hBd
        omega
    · obtain ⟨s, hs, hC⟩ := Set.mem_iUnion₂.1 hcC
      obtain ⟨h0, -, -, -, hp⟩ := hC
      have hsS := (mem_Sc.1 hs)
      rcases hX with ⟨s', hs', hC'⟩ | hBd
      · obtain ⟨h0', -, -, -, hp'⟩ := hC'
        have hss' : s = s' := by omega
        subst hss'
        exact Set.disjoint_left.1 disjoint_splitPairs_ddPairs hp hp'
      · obtain ⟨h0', -, -, -⟩ := hBd
        omega
  rw [decided_splitTail_inter_e2Box hK hπ]
  simp only [Nat.card_coe_set_eq]
  rw [Set.ncard_union_eq hd1, Set.ncard_union_eq hd2, Set.ncard_union_eq hdBC,
    ncard_biUnion_eq _ _ bBox_pairwise, ncard_biUnion_eq _ _ cBox_pairwise]

/-- ★★ **The inertTail count**: exact at every level. -/
theorem card_decided_inertTail {K : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) :
    Nat.card ((decidedSet O 4 inertTailType K ∩ e2Box O K) : Set (Coeff O 4 K))
      = (∑ s ∈ Sc K, Nat.card ((cBox π K s (irrPairs (ResidueField O)))
            : Set (Coeff O 4 K)))
        + (Nat.card ((decidedSet O 4 inertTailType K ∩ e2DdBox π K) : Set (Coeff O 4 K))
          + Nat.card ((decidedSet O 4 inertTailType K ∩ bdBox O K) : Set (Coeff O 4 K))) := by
  have hd2 : Disjoint (decidedSet O 4 inertTailType K ∩ e2DdBox π K)
      (decidedSet O 4 inertTailType K ∩ bdBox O K) := by
    rw [Set.disjoint_left]
    rintro c ⟨-, hD⟩ ⟨-, hBd⟩
    rw [e2DdBox_eq] at hD
    obtain ⟨s, hs, hC⟩ := Set.mem_iUnion₂.1 hD
    obtain ⟨h0, -, -, -, -⟩ := hC
    obtain ⟨h0', -, -, -⟩ := hBd
    have := (mem_Sc.1 hs).2
    omega
  have hd1 : Disjoint (⋃ s ∈ Sc K, cBox π K s (irrPairs (ResidueField O)))
      ((decidedSet O 4 inertTailType K ∩ e2DdBox π K)
        ∪ (decidedSet O 4 inertTailType K ∩ bdBox O K)) := by
    rw [Set.disjoint_left]
    intro c hcC hcX
    obtain ⟨s, hs, hC⟩ := Set.mem_iUnion₂.1 hcC
    obtain ⟨h0, -, -, -, hp⟩ := hC
    rcases hcX with ⟨-, hD⟩ | ⟨-, hBd⟩
    · rw [e2DdBox_eq] at hD
      obtain ⟨s', hs', hC'⟩ := Set.mem_iUnion₂.1 hD
      obtain ⟨h0', -, -, -, hp'⟩ := hC'
      have hss' : s = s' := by omega
      subst hss'
      exact Set.disjoint_left.1 disjoint_irrPairs_ddPairs hp hp'
    · obtain ⟨h0', -, -, -⟩ := hBd
      have := (mem_Sc.1 hs).2
      omega
  rw [decided_inertTail_inter_e2Box hK hπ]
  simp only [Nat.card_coe_set_eq]
  rw [Set.ncard_union_eq hd1, Set.ncard_union_eq hd2, ncard_biUnion_eq _ _ cBox_pairwise]

/-! ### §6b — the stratum counts -/

private theorem quad_box_eq {K : ℕ} (S₀ S₁ S₂ S₃ : Set (Res O K)) :
    ({c : Coeff O 4 K | c 0 ∈ S₀ ∧ c 1 ∈ S₁ ∧ c 2 ∈ S₂ ∧ c 3 ∈ S₃}
        : Set (Coeff O 4 K))
      = {c : Coeff O 4 K | ∀ i : Fin 4,
          c i ∈ (if (i : ℕ) = 0 then S₀ else if (i : ℕ) = 1 then S₁
            else if (i : ℕ) = 2 then S₂ else S₃)} := by
  ext c
  constructor
  · rintro ⟨h0, h1, h2, h3⟩ i
    by_cases hi0 : (i : ℕ) = 0
    · rw [if_pos hi0, show i = 0 from Fin.ext hi0]
      exact h0
    · rw [if_neg hi0]
      by_cases hi1 : (i : ℕ) = 1
      · rw [if_pos hi1, show i = 1 from Fin.ext hi1]
        exact h1
      · rw [if_neg hi1]
        by_cases hi2 : (i : ℕ) = 2
        · rw [if_pos hi2, show i = 2 from Fin.ext hi2]
          exact h2
        · rw [if_neg hi2]
          have hieq : i = 3 := by
            have h5 := i.isLt
            exact Fin.ext (by omega)
          rw [hieq]
          exact h3
  · intro hall
    have h0 := hall 0
    have h1 := hall 1
    have h2 := hall 2
    have h3 := hall 3
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

private theorem quad_box_card {K : ℕ} (S₀ S₁ S₂ S₃ : Set (Res O K)) :
    Nat.card ({c : Coeff O 4 K | c 0 ∈ S₀ ∧ c 1 ∈ S₁ ∧ c 2 ∈ S₂ ∧ c 3 ∈ S₃}
        : Set (Coeff O 4 K))
      = Nat.card S₀ * Nat.card S₁ * Nat.card S₂ * Nat.card S₃ := by
  rw [quad_box_eq, card_pi_set, Fin.prod_univ_four]
  rw [if_pos (show ((0 : Fin 4) : ℕ) = 0 from rfl)]
  rw [if_neg (show ¬ ((1 : Fin 4) : ℕ) = 0 by decide),
    if_pos (show ((1 : Fin 4) : ℕ) = 1 from rfl)]
  rw [if_neg (show ¬ ((2 : Fin 4) : ℕ) = 0 by decide),
    if_neg (show ¬ ((2 : Fin 4) : ℕ) = 1 by decide),
    if_pos (show ((2 : Fin 4) : ℕ) = 2 from rfl)]
  rw [if_neg (show ¬ ((3 : Fin 4) : ℕ) = 0 by decide),
    if_neg (show ¬ ((3 : Fin 4) : ℕ) = 1 by decide),
    if_neg (show ¬ ((3 : Fin 4) : ℕ) = 2 by decide)]

/-- ★ The genre-(a) stratum count: `(q−1)²·q^(4K−3t−5)`. -/
theorem card_aBox {K t : ℕ} (hK : 3 ≤ K) (ht : 2 ≤ t) (htK : 2 * t < K) :
    Nat.card (aBox O K t : Set (Coeff O 4 K))
      = (residueCard O - 1) * (residueCard O - 1)
        * residueCard O ^ (4 * K - (3 * t + 5)) := by
  have hbox : (aBox O K t : Set (Coeff O 4 K))
      = {c : Coeff O 4 K | c 0 ∈ {x : Res O K | resOrd x = 2 * t}
          ∧ c 1 ∈ {x : Res O K | t + 1 ≤ resOrd x}
          ∧ c 2 ∈ {x : Res O K | resOrd x = 1}
          ∧ c 3 ∈ {x : Res O K | 1 ≤ resOrd x}} := rfl
  rw [hbox, quad_box_card,
    card_setOf_resOrd_eq (show 2 * t < K by omega),
    card_setOf_le_resOrd (show t + 1 ≤ K by omega),
    card_setOf_resOrd_eq (show 1 < K by omega),
    card_setOf_le_resOrd (show 1 ≤ K by omega)]
  rw [show K - 1 - 1 = K - 2 from by omega,
    show 4 * K - (3 * t + 5)
      = (K - 2 * t - 1) + ((K - (t + 1)) + ((K - 2) + (K - 1))) from by omega,
    pow_add, pow_add, pow_add]
  ring

/-- ★ The genre-(b) stratum count: `(q−1)²·q^(4K−3v−4)`. -/
theorem card_bBox {K v : ℕ} (hK : 3 ≤ K) (hv : 2 ≤ v) (hvK : 2 * v ≤ K) :
    Nat.card (bBox O K v : Set (Coeff O 4 K))
      = (residueCard O - 1) * (residueCard O - 1)
        * residueCard O ^ (4 * K - (3 * v + 4)) := by
  have hbox : (bBox O K v : Set (Coeff O 4 K))
      = {c : Coeff O 4 K | c 0 ∈ {x : Res O K | 2 * v ≤ resOrd x}
          ∧ c 1 ∈ {x : Res O K | resOrd x = v}
          ∧ c 2 ∈ {x : Res O K | resOrd x = 1}
          ∧ c 3 ∈ {x : Res O K | 1 ≤ resOrd x}} := rfl
  rw [hbox, quad_box_card,
    card_setOf_le_resOrd (show 2 * v ≤ K by omega),
    card_setOf_resOrd_eq (show v < K by omega),
    card_setOf_resOrd_eq (show 1 < K by omega),
    card_setOf_le_resOrd (show 1 ≤ K by omega)]
  rw [show K - 1 - 1 = K - 2 from by omega,
    show 4 * K - (3 * v + 4)
      = (K - 2 * v) + ((K - v - 1) + ((K - 2) + (K - 1))) from by omega,
    pow_add, pow_add, pow_add]
  ring

/-- ★ The boundary bound: `#bdBox ≤ q^(3K)`. -/
theorem card_bdBox_le {K : ℕ} (hK : 3 ≤ K) :
    Nat.card (bdBox O K : Set (Coeff O 4 K)) ≤ residueCard O ^ (3 * K) := by
  have hsub : (bdBox O K : Set (Coeff O 4 K))
      ⊆ {c : Coeff O 4 K | c 0 ∈ {x : Res O K | K ≤ resOrd x}
          ∧ c 1 ∈ {x : Res O K | 0 ≤ resOrd x}
          ∧ c 2 ∈ {x : Res O K | 0 ≤ resOrd x}
          ∧ c 3 ∈ {x : Res O K | 0 ≤ resOrd x}} := by
    rintro c ⟨h0, h1, h2, h3⟩
    exact ⟨h0, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  refine le_trans (Nat.card_mono (Set.toFinite _) hsub) ?_
  rw [quad_box_card,
    card_setOf_le_resOrd (le_refl K),
    card_setOf_le_resOrd (show 0 ≤ K by omega)]
  rw [Nat.sub_self, pow_zero, one_mul, Nat.sub_zero, ← pow_add, ← pow_add]
  exact le_of_eq (by rw [show K + K + K = 3 * K from by ring])

end Counts

/-! ### §6c — the genre-(c) digit-triple engine -/

/-- The digit triples `(δ, d₁, d₀)` whose monic normalization lies in the pair set. -/
def digTriples (F : Type*) [Field F] (P : Set (F × F)) : Set (F × F × F) :=
  {x | x.1 ≠ 0 ∧ (x.2.1 / x.1, x.2.2 / x.1) ∈ P}

/-- The triple count: `(q−1)·#P` (the scaling bijection). -/
theorem card_digTriples {F : Type*} [Field F] [Finite F] (P : Set (F × F)) :
    Nat.card (digTriples F P) = (Nat.card F - 1) * Nat.card P := by
  classical
  have hequiv : ({δ : F // δ ≠ 0} × P) ≃ digTriples F P :=
    { toFun := fun x =>
        ⟨(x.1.1, x.1.1 * x.2.1.1, x.1.1 * x.2.1.2), x.1.2, by
          have h1 : x.1.1 * x.2.1.1 / x.1.1 = x.2.1.1 := by
            rw [mul_comm, mul_div_assoc, div_self x.1.2, mul_one]
          have h2 : x.1.1 * x.2.1.2 / x.1.1 = x.2.1.2 := by
            rw [mul_comm, mul_div_assoc, div_self x.1.2, mul_one]
          show ((x.1.1 * x.2.1.1) / x.1.1, (x.1.1 * x.2.1.2) / x.1.1) ∈ P
          rw [h1, h2]
          exact x.2.2⟩
      invFun := fun x =>
        (⟨x.1.1, x.2.1⟩, ⟨(x.1.2.1 / x.1.1, x.1.2.2 / x.1.1), x.2.2⟩)
      left_inv := fun x => by
        refine Prod.ext (Subtype.ext rfl) (Subtype.ext (Prod.ext ?_ ?_))
        · show x.1.1 * x.2.1.1 / x.1.1 = x.2.1.1
          rw [mul_comm, mul_div_assoc, div_self x.1.2, mul_one]
        · show x.1.1 * x.2.1.2 / x.1.1 = x.2.1.2
          rw [mul_comm, mul_div_assoc, div_self x.1.2, mul_one]
      right_inv := fun x => by
        refine Subtype.ext (Prod.ext rfl (Prod.ext ?_ ?_))
        · show x.1.1 * (x.1.2.1 / x.1.1) = x.1.2.1
          rw [mul_comm]
          exact div_mul_cancel₀ _ x.2.1
        · show x.1.1 * (x.1.2.2 / x.1.1) = x.1.2.2
          rw [mul_comm]
          exact div_mul_cancel₀ _ x.2.1 }
  rw [← Nat.card_congr hequiv, Nat.card_prod]
  congr 1
  have hset : ({δ : F | δ ≠ 0} : Set F) = Set.univ \ {0} := by
    ext δ
    simp
  rw [show {δ : F // δ ≠ 0} = ({δ : F | δ ≠ 0} : Set F) from rfl, Nat.card_coe_set_eq,
    hset, Set.ncard_sdiff (by simp : ({0} : Set F) ⊆ Set.univ), Set.ncard_univ,
    Set.ncard_singleton]

section CBoxCount

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

-- IFCG36's private fibre helpers, reproduced (the sanctioned replay).
private theorem natCard_set_eq_card_filter {γ : Type*} [Fintype γ] (s : Set γ) :
    Nat.card s = (Finset.univ.filter (fun a => a ∈ s)).card := by
  classical
  rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset (Finset.univ.filter (fun a => a ∈ s))]
  congr 1
  ext a
  simp

private theorem natCard_eq_sum_fiber {γ δ : Type*} [Fintype γ] (s : Set γ) (φ : γ → δ)
    (T : Finset δ) (hT : ∀ a ∈ s, φ a ∈ T) :
    Nat.card s = ∑ b ∈ T, Nat.card ((s ∩ φ ⁻¹' {b}) : Set γ) := by
  classical
  rw [natCard_set_eq_card_filter,
    Finset.card_eq_sum_card_fiberwise (f := φ) (t := T)
      (fun a ha => hT a (by simpa using (Finset.mem_filter.1 ha).2))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [natCard_set_eq_card_filter, Finset.filter_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/-- ★★ The genre-(c) stratum count: `#(digTriples P)·q^(4K−3s−7)` — DBL's digit
instrument replayed on the width-2 face. -/
theorem card_cBox {K s : ℕ} (hK : 3 ≤ K) {π : O} (hπ : Irreducible π) (hs : 1 ≤ s)
    (hsK : 2 * s + 1 < K) {P : Set (ResidueField O × ResidueField O)}
    (hP : ∀ p ∈ P, p.2 ≠ 0) :
    Nat.card (cBox π K s P : Set (Coeff O 4 K))
      = Nat.card (digTriples (ResidueField O) P)
        * residueCard O ^ (4 * K - (3 * s + 7)) := by
  classical
  letI : Fintype (Coeff O 4 K) := Fintype.ofFinite _
  letI : Fintype (ResidueField O) := Fintype.ofFinite _
  set T : Finset (ResidueField O × ResidueField O × ResidueField O) :=
    Finset.univ.filter (fun x => x ∈ digTriples (ResidueField O) P) with hTdef
  have hT : ∀ c ∈ (cBox π K s P : Set (Coeff O 4 K)),
      (resDig π 1 (c 2), resDig π (s + 1) (c 1), resDig π (2 * s + 1) (c 0)) ∈ T := by
    rintro c ⟨h0, h1, h2, h3, hp⟩
    rw [hTdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · show resDig π 1 (c 2) ≠ 0
      exact ((resOrd_eq_iff_resDig hπ (by omega) (c 2)).1 h2).2
    · exact hp
  rw [natCard_eq_sum_fiber _
    (fun c => (resDig π 1 (c 2), resDig π (s + 1) (c 1), resDig π (2 * s + 1) (c 0)))
    T hT]
  have hfiber : ∀ b ∈ T,
      Nat.card (((cBox π K s P : Set (Coeff O 4 K))
          ∩ (fun c : Coeff O 4 K =>
              (resDig π 1 (c 2), resDig π (s + 1) (c 1), resDig π (2 * s + 1) (c 0)))
            ⁻¹' {b}) : Set (Coeff O 4 K))
        = residueCard O ^ (4 * K - (3 * s + 7)) := by
    intro b hb
    rw [hTdef, Finset.mem_filter] at hb
    obtain ⟨-, hbδ, hbP⟩ := hb
    have hb22 : b.2.2 ≠ 0 := by
      intro h6
      exact (hP _ hbP) (by rw [h6, zero_div])
    have hset : ((cBox π K s P : Set (Coeff O 4 K))
        ∩ (fun c : Coeff O 4 K =>
            (resDig π 1 (c 2), resDig π (s + 1) (c 1), resDig π (2 * s + 1) (c 0)))
          ⁻¹' {b})
        = {c : Coeff O 4 K |
            c 0 ∈ {x : Res O K | 2 * s + 1 ≤ resOrd x ∧ resDig π (2 * s + 1) x = b.2.2}
            ∧ c 1 ∈ {x : Res O K | s + 1 ≤ resOrd x ∧ resDig π (s + 1) x = b.2.1}
            ∧ c 2 ∈ {x : Res O K | 1 ≤ resOrd x ∧ resDig π 1 x = b.1}
            ∧ c 3 ∈ {x : Res O K | 1 ≤ resOrd x}} := by
      ext c
      constructor
      · rintro ⟨⟨h0, h1, h2, h3, hp⟩, hpre⟩
        have hb' : (resDig π 1 (c 2), resDig π (s + 1) (c 1),
            resDig π (2 * s + 1) (c 0)) = b := hpre
        have e1 : resDig π 1 (c 2) = b.1 := by rw [← hb']
        have e2 : resDig π (s + 1) (c 1) = b.2.1 := by rw [← hb']
        have e3 : resDig π (2 * s + 1) (c 0) = b.2.2 := by rw [← hb']
        exact ⟨⟨by omega, e3⟩, ⟨h1, e2⟩, ⟨by omega, e1⟩, h3⟩
      · rintro ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩, ⟨h2a, h2b⟩, h3⟩
        have h0 : resOrd (c 0) = 2 * s + 1 :=
          (resOrd_eq_iff_resDig hπ (by omega) (c 0)).2 ⟨h0a, by rw [h0b]; exact hb22⟩
        have h2 : resOrd (c 2) = 1 :=
          (resOrd_eq_iff_resDig hπ (by omega) (c 2)).2 ⟨h2a, by rw [h2b]; exact hbδ⟩
        have hp : cPair π s c ∈ P := by
          show (resDig π (s + 1) (c 1) / resDig π 1 (c 2),
            resDig π (2 * s + 1) (c 0) / resDig π 1 (c 2)) ∈ P
          rw [h0b, h1b, h2b]
          exact hbP
        refine ⟨⟨h0, h1a, h2, h3, hp⟩, ?_⟩
        show (resDig π 1 (c 2), resDig π (s + 1) (c 1),
          resDig π (2 * s + 1) (c 0)) = b
        exact Prod.ext h2b (Prod.ext h1b h0b)
    rw [hset, quad_box_card,
      card_setOf_resDig hπ (show 2 * s + 1 < K by omega) b.2.2,
      card_setOf_resDig hπ (show s + 1 < K by omega) b.2.1,
      card_setOf_resDig hπ (show 1 < K by omega) b.1,
      card_setOf_le_resOrd (show 1 ≤ K by omega)]
    rw [show 4 * K - (3 * s + 7)
      = (K - (2 * s + 1 + 1)) + ((K - (s + 1 + 1)) + ((K - (1 + 1)) + (K - 1)))
        from by omega, pow_add, pow_add, pow_add]
    ring
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [hTdef, ← natCard_set_eq_card_filter]

end CBoxCount

/-! ## §7 — the limit layer -/

section Limits

open Filter Topology

/-- **The named E2 dd-recursion family** — the ONE open premise carrier of this file's
laws (the exact analogue of ER4's `e1DdDecFam`; the linear-recentring depth ≥ 1 tower,
out of IFCG20/43's landed reach — see the module docstring's recursion fence). -/
def e2DdDecFam (σ : FactorizationType) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    (Nat.card ((decidedSet O 4 σ (M + 4) ∩ e2DdBox π (M + 4))
        : Set (Coeff O 4 (M + 4))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- The normalized boundary term (squeezed to `0` below). -/
def e2BdDecFam (σ : FactorizationType) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ _ M =>
    (Nat.card ((decidedSet O 4 σ (M + 4) ∩ bdBox O (M + 4))
        : Set (Coeff O 4 (M + 4))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- The genre-(a) depth-0 family (the ramPair carrier). -/
def e2Ram0Fam :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ _ M =>
    ((∑ t ∈ Ta (M + 4), Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4)))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- The genre-(b) + genre-(c)-split depth-0 family (the splitTail carrier). -/
def e2Split0Fam :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    (((∑ v ∈ Vb (M + 4), Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4))))
        + ∑ s ∈ Sc (M + 4),
            Nat.card ((cBox π (M + 4) s (splitPairs (ResidueField O)))
              : Set (Coeff O 4 (M + 4)))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- The genre-(c)-irreducible depth-0 family (the inertTail carrier). -/
def e2Inert0Fam :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ :=
  fun O _ _ _ _ _ π M =>
    ((∑ s ∈ Sc (M + 4),
        Nat.card ((cBox π (M + 4) s (irrPairs (ResidueField O)))
          : Set (Coeff O 4 (M + 4)))) : ℝ)
      / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))

/-- ★ **The squeeze combinator**: a family trapped between a `ZcURLim` family and its
translate by a vanishing error is `ZcURLim` (the boundary-cell eater). -/
theorem ZcURLim.sandwich
    {F G E : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)], O → ℕ → ℝ}
    (hG : ZcURLim G)
    (hE : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ π : O, Irreducible π → Filter.Tendsto (E O π) Filter.atTop (nhds 0))
    (h1 : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ π : O, Irreducible π → ∀ M, G O π M ≤ F O π M)
    (h2 : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ π : O, Irreducible π → ∀ M, F O π M ≤ G O π M + E O π M) :
    ZcURLim F := by
  obtain ⟨n, d, hd, hval⟩ := hG
  refine ⟨n, d, hd, ?_⟩
  intro O _ _ _ _ _
  obtain ⟨hne, hlim⟩ := hval O
  refine ⟨hne, ?_⟩
  intro π hπ
  have hlim2 : Filter.Tendsto (fun M => G O π M + E O π M) Filter.atTop
      (nhds (((n.eval ((residueCard O : ℕ) : ℚ)
        / d.eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ) + 0)) :=
    (hlim π hπ).add (hE O π hπ)
  rw [add_zero] at hlim2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (hlim π hπ) hlim2
    (h1 O π hπ) (h2 O π hπ)

/-- ★ **The stratum-sum limit machine**: partial geometric sums over a window running
off to infinity converge to the full geometric value `C·q³/((q³−1)·q^(3a+e))`. -/
theorem tendsto_geom_sum {q : ℝ} (hq : 2 ≤ q) (C : ℝ) (a e : ℕ)
    (T : ℕ → ℕ) (hT : Filter.Tendsto T Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun M => ∑ t ∈ Finset.Ico a (T M), C / q ^ (3 * t + e))
      Filter.atTop (nhds (C * q ^ 3 / ((q ^ 3 - 1) * q ^ (3 * a + e)))) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hq3 : (0 : ℝ) < q ^ 3 := by positivity
  have h8 : (8 : ℝ) ≤ q ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := by gcongr
  have hr : |1 / q ^ 3| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hq3]
    linarith
  have hgeo := (hasSum_geometric_of_abs_lt_one hr).mul_left (C / q ^ (3 * a + e))
  have hfun : ∀ j : ℕ, C / q ^ (3 * a + e) * (1 / q ^ 3) ^ j
      = C / q ^ (3 * (a + j) + e) := by
    intro j
    rw [show 3 * (a + j) + e = (3 * a + e) + 3 * j from by ring, pow_add, pow_mul]
    rw [div_pow, one_pow, div_mul_div_comm, mul_one]
    congr 1
    rw [pow_add, pow_add, pow_mul, pow_mul]
  have hval : C / q ^ (3 * a + e) * (1 - 1 / q ^ 3)⁻¹
      = C * q ^ 3 / ((q ^ 3 - 1) * q ^ (3 * a + e)) := by
    have h1 : q ^ 3 - 1 ≠ 0 := by intro h; linarith
    have h2 : (1 : ℝ) - 1 / q ^ 3 ≠ 0 := by
      have hlt : 1 / q ^ 3 < 1 := by rw [div_lt_one hq3]; linarith
      intro h
      linarith
    have h3 : q ^ (3 * a + e) ≠ 0 := by positivity
    field_simp
  simp only [hfun] at hgeo
  rw [hval] at hgeo
  have htend := hgeo.tendsto_sum_nat
  have hTa : Filter.Tendsto (fun M => T M - a) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop] at hT ⊢
    intro b
    obtain ⟨N, hN⟩ := hT (b + a)
    exact ⟨N, fun M hM => by have := hN M hM; omega⟩
  have hcomp := htend.comp hTa
  refine hcomp.congr ?_
  intro M
  show ∑ j ∈ Finset.range (T M - a), C / q ^ (3 * (a + j) + e)
    = ∑ t ∈ Finset.Ico a (T M), C / q ^ (3 * t + e)
  rw [Finset.sum_Ico_eq_sum_range]

-- the index-window normalizations
private theorem Ta_eq (K : ℕ) : Ta K = Finset.Ico 2 ((K + 1) / 2) := by
  ext t
  rw [mem_Ta, Finset.mem_Ico]
  omega

private theorem Vb_eq (K : ℕ) : Vb K = Finset.Ico 2 (K / 2 + 1) := by
  ext v
  rw [mem_Vb, Finset.mem_Ico]
  omega

private theorem Sc_eq (K : ℕ) : Sc K = Finset.Ico 1 (K / 2) := by
  ext s
  rw [mem_Sc, Finset.mem_Ico]
  omega

private theorem tendsto_Ta_window : Filter.Tendsto (fun M : ℕ => (M + 4 + 1) / 2)
    Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨2 * b, fun M hM => by omega⟩

private theorem tendsto_Vb_window : Filter.Tendsto (fun M : ℕ => (M + 4) / 2 + 1)
    Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨2 * b, fun M hM => by omega⟩

private theorem tendsto_Sc_window : Filter.Tendsto (fun M : ℕ => (M + 4) / 2)
    Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨2 * b, fun M hM => by omega⟩

/-! ### §7b — the pair-set cardinality values -/

section PairCounts

variable {F : Type*} [Field F] [Finite F]

private theorem card_ne_zero_subtype : Nat.card {x : F // x ≠ 0} = Nat.card F - 1 := by
  have hset : ({δ : F | δ ≠ 0} : Set F) = Set.univ \ {0} := by
    ext δ
    simp
  rw [show {δ : F // δ ≠ 0} = ({δ : F | δ ≠ 0} : Set F) from rfl, Nat.card_coe_set_eq,
    hset, Set.ncard_sdiff (by simp : ({0} : Set F) ⊆ Set.univ), Set.ncard_univ,
    Set.ncard_singleton]

private theorem pairs_ne_zero_eq :
    {p : F × F | p.2 ≠ 0} = splitPairs F ∪ irrPairs F ∪ ddPairs F := by
  ext p
  constructor
  · intro hp
    rcases pair_trichotomy hp with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · rintro ((h | h) | h)
    · exact splitPairs_snd_ne_zero h
    · exact irrPairs_snd_ne_zero h
    · exact ddPairs_snd_ne_zero h

private theorem card_pairs_ne_zero :
    Nat.card ({p : F × F | p.2 ≠ 0} : Set (F × F)) = Nat.card F * (Nat.card F - 1) := by
  have hequiv : (F × {x : F // x ≠ 0}) ≃ ({p : F × F | p.2 ≠ 0} : Set (F × F)) :=
    { toFun := fun x => ⟨(x.1, x.2.1), x.2.2⟩
      invFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
      left_inv := fun x => Prod.ext rfl (Subtype.ext rfl)
      right_inv := fun p => Subtype.ext rfl }
  rw [← Nat.card_congr hequiv, Nat.card_prod, card_ne_zero_subtype]

private theorem card_pair_partition :
    Nat.card (splitPairs F) + Nat.card (irrPairs F) + Nat.card (ddPairs F)
      = Nat.card F * (Nat.card F - 1) := by
  rw [← card_pairs_ne_zero, pairs_ne_zero_eq]
  simp only [Nat.card_coe_set_eq]
  rw [Set.ncard_union_eq (by
      rw [Set.disjoint_union_left]
      exact ⟨disjoint_splitPairs_ddPairs, disjoint_irrPairs_ddPairs⟩),
    Set.ncard_union_eq disjoint_splitPairs_irrPairs]

private theorem two_mul_card_irrPairs :
    2 * Nat.card (irrPairs F) = Nat.card F ^ 2 - Nat.card F := by
  letI : Fintype F := Fintype.ofFinite F
  rw [card_irrPairs, two_mul_card_irredOfDeg_two F]
  simp [Nat.card_eq_fintype_card]

end PairCounts

/-! ### §7c — the three depth-0 `ZcURLim` fires -/

/-- ★★ **The genre-(a) limit**: value `(q−1)²·q³ / ((q³−1)·q¹¹)` — the fractional-corner
geometric series, resummed. -/
theorem zcURLim_e2Ram0Fam : ZcURLim e2Ram0Fam := by
  refine ⟨(Polynomial.X - 1) ^ 2 * Polynomial.X ^ 3,
    (Polynomial.X ^ 3 - 1) * Polynomial.X ^ 11, ?_, ?_⟩
  · refine mul_ne_zero ?_ (pow_ne_zero _ Polynomial.X_ne_zero)
    intro h
    have h2 := congrArg (Polynomial.eval (0 : ℚ)) h
    simp at h2
  · intro O _ _ _ _ _
    have hq2 : 2 ≤ residueCard O := two_le_residueCard O
    have hqQ : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast hq2
    have hqQ0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := by linarith
    have h8 : (8 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) ^ 3 := by
      calc (8 : ℚ) = 2 ^ 3 := by norm_num
        _ ≤ _ := by gcongr
    have hd3 : ((residueCard O : ℕ) : ℚ) ^ 3 - 1 ≠ 0 := by
      intro h
      have h2 := sub_eq_zero.1 h
      linarith
    refine ⟨?_, ?_⟩
    · rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
      exact mul_ne_zero hd3 (pow_ne_zero _ hqQ0)
    · intro π hπ
      have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast hq2
      have hM : ∀ M, e2Ram0Fam O π M
          = ∑ t ∈ Finset.Ico 2 ((M + 4 + 1) / 2),
              ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1))
                / ((residueCard O : ℕ) : ℝ) ^ (3 * t + 5) := by
        intro M
        show ((∑ t ∈ Ta (M + 4),
            Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4)))) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) = _
        rw [Ta_eq, Finset.sum_div]
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Finset.mem_Ico] at ht
        rw [card_aBox (by omega) ht.1 (by omega)]
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_sub (by omega : 1 ≤ residueCard O), Nat.cast_one]
        obtain ⟨E, hE1, hE2⟩ : ∃ E, 4 * (M + 4) - (3 * t + 5) = E
            ∧ 4 * (M + 4) = E + (3 * t + 5) := ⟨_, rfl, by omega⟩
        rw [hE1, hE2, pow_add,
          mul_comm (((residueCard O : ℕ) : ℝ) ^ E) (((residueCard O : ℕ) : ℝ) ^ (3 * t + 5)),
          mul_div_mul_right _ _ (pow_ne_zero E (by positivity))]
      have hlim := tendsto_geom_sum (q := ((residueCard O : ℕ) : ℝ)) hq2R
        ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)) 2 5 _
        tendsto_Ta_window
      have hval : ((((Polynomial.X - 1) ^ 2 * Polynomial.X ^ 3 : Polynomial ℚ).eval
            ((residueCard O : ℕ) : ℚ)
          / ((Polynomial.X ^ 3 - 1) * Polynomial.X ^ 11 : Polynomial ℚ).eval
            ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
          = (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
            * ((residueCard O : ℕ) : ℝ) ^ 3
            / ((((residueCard O : ℕ) : ℝ) ^ 3 - 1)
              * ((residueCard O : ℕ) : ℝ) ^ (3 * 2 + 5)) := by
        rw [Rat.cast_div]
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one]
        push_cast
        ring
      rw [hval]
      exact hlim.congr (fun M => (hM M).symm)

section ValueBridge

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

private theorem hQF : Nat.card (ResidueField O) = residueCard O := rfl

/-- The split-pair prefactor, closed in `q`: `(q−1)·#split = (q−1)·(q−1)(q−2)/2`. -/
private theorem digTriples_split_val :
    ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1)
        * ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 2)) / 2 := by
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hQ1 : 1 ≤ Nat.card (ResidueField O) := by rw [hQF]; omega
  have hpart := card_pair_partition (F := ResidueField O)
  have hirr := two_mul_card_irrPairs (F := ResidueField O)
  have hddc := IFCG36.card_ddPairs (F := ResidueField O)
  have hpartR : ((Nat.card (splitPairs (ResidueField O))) : ℝ)
      + ((Nat.card (irrPairs (ResidueField O))) : ℝ)
      + ((Nat.card (ddPairs (ResidueField O))) : ℝ)
      = ((residueCard O : ℕ) : ℝ) * (((residueCard O : ℕ) : ℝ) - 1) := by
    have h := congrArg (Nat.cast (R := ℝ)) hpart
    push_cast [hQF, Nat.cast_sub (show 1 ≤ residueCard O by omega)] at h
    exact_mod_cast h
  have hirrR : 2 * ((Nat.card (irrPairs (ResidueField O))) : ℝ)
      = ((residueCard O : ℕ) : ℝ) ^ 2 - ((residueCard O : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hirr
    push_cast [hQF, Nat.cast_sub (show residueCard O ≤ residueCard O ^ 2 from Nat.le_self_pow (by norm_num) _)] at h
    exact_mod_cast h
  have hddR : ((Nat.card (ddPairs (ResidueField O))) : ℝ)
      = ((residueCard O : ℕ) : ℝ) - 1 := by
    have h := congrArg (Nat.cast (R := ℝ)) hddc
    push_cast [hQF, Nat.cast_sub (show 1 ≤ residueCard O by omega)] at h
    exact_mod_cast h
  have hsplitR : 2 * ((Nat.card (splitPairs (ResidueField O))) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 2) := by
    linear_combination 2 * hpartR - hirrR - 2 * hddR
  have hdt := card_digTriples (splitPairs (ResidueField O))
  have hdtR : ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1)
        * ((Nat.card (splitPairs (ResidueField O))) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hdt
    push_cast [hQF, Nat.cast_sub (show 1 ≤ residueCard O by omega)] at h
    exact_mod_cast h
  rw [hdtR]
  linear_combination ((((residueCard O : ℕ) : ℝ) - 1) / 2) * hsplitR

/-- The irreducible-pair prefactor, closed in `q`: `(q−1)·#irr = (q−1)·(q²−q)/2`. -/
private theorem digTriples_irr_val :
    ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1)
        * ((((residueCard O : ℕ) : ℝ) ^ 2 - ((residueCard O : ℕ) : ℝ))) / 2 := by
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hQ1 : 1 ≤ Nat.card (ResidueField O) := by rw [hQF]; omega
  have hirr := two_mul_card_irrPairs (F := ResidueField O)
  have hirrR : 2 * ((Nat.card (irrPairs (ResidueField O))) : ℝ)
      = ((residueCard O : ℕ) : ℝ) ^ 2 - ((residueCard O : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hirr
    push_cast [hQF, Nat.cast_sub (show residueCard O ≤ residueCard O ^ 2 from Nat.le_self_pow (by norm_num) _)] at h
    exact_mod_cast h
  have hdt := card_digTriples (irrPairs (ResidueField O))
  have hdtR : ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ)
      = (((residueCard O : ℕ) : ℝ) - 1)
        * ((Nat.card (irrPairs (ResidueField O))) : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hdt
    push_cast [hQF, Nat.cast_sub (show 1 ≤ residueCard O by omega)] at h
    exact_mod_cast h
  rw [hdtR]
  linear_combination ((((residueCard O : ℕ) : ℝ) - 1) / 2) * hirrR

end ValueBridge

/-- ★★ **The genre-(b) + (c)-split limit**: value `(q−1)²·q⁴ / (2(q³−1)·q¹⁰)`. -/
theorem zcURLim_e2Split0Fam : ZcURLim e2Split0Fam := by
  refine ⟨(Polynomial.X - 1) ^ 2 * Polynomial.X ^ 4,
    Polynomial.C 2 * ((Polynomial.X ^ 3 - 1) * Polynomial.X ^ 10), ?_, ?_⟩
  · refine mul_ne_zero (Polynomial.C_ne_zero.mpr two_ne_zero)
      (mul_ne_zero ?_ (pow_ne_zero _ Polynomial.X_ne_zero))
    intro h
    have h2 := congrArg (Polynomial.eval (0 : ℚ)) h
    simp at h2
  · intro O _ _ _ _ _
    have hq2 : 2 ≤ residueCard O := two_le_residueCard O
    have hqQ : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast hq2
    have hqQ0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := by linarith
    have h8 : (8 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) ^ 3 := by
      calc (8 : ℚ) = 2 ^ 3 := by norm_num
        _ ≤ _ := by gcongr
    have hd3 : ((residueCard O : ℕ) : ℚ) ^ 3 - 1 ≠ 0 := by
      intro h
      have h2 := sub_eq_zero.1 h
      linarith
    refine ⟨?_, ?_⟩
    · rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one]
      exact mul_ne_zero two_ne_zero (mul_ne_zero hd3 (pow_ne_zero _ hqQ0))
    · intro π hπ
      have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast hq2
      have hM : ∀ M, e2Split0Fam O π M
          = (∑ v ∈ Finset.Ico 2 ((M + 4) / 2 + 1),
              ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1))
                / ((residueCard O : ℕ) : ℝ) ^ (3 * v + 4))
            + ∑ s ∈ Finset.Ico 1 ((M + 4) / 2),
              ((Nat.card (digTriples (ResidueField O)
                  (splitPairs (ResidueField O)))) : ℝ)
                / ((residueCard O : ℕ) : ℝ) ^ (3 * s + 7) := by
        intro M
        show (((∑ v ∈ Vb (M + 4),
              Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4))))
            + ∑ s ∈ Sc (M + 4),
                Nat.card ((cBox π (M + 4) s (splitPairs (ResidueField O)))
                  : Set (Coeff O 4 (M + 4)))) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) = _
        rw [add_div]
        congr 1
        · rw [Vb_eq, Nat.cast_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun v hv => ?_
          rw [Finset.mem_Ico] at hv
          rw [card_bBox (by omega) hv.1 (by omega)]
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
            Nat.cast_sub (by omega : 1 ≤ residueCard O), Nat.cast_one]
          obtain ⟨E, hE1, hE2⟩ : ∃ E, 4 * (M + 4) - (3 * v + 4) = E
              ∧ 4 * (M + 4) = E + (3 * v + 4) := ⟨_, rfl, by omega⟩
          rw [hE1, hE2, pow_add,
            mul_comm (((residueCard O : ℕ) : ℝ) ^ E)
              (((residueCard O : ℕ) : ℝ) ^ (3 * v + 4)),
            mul_div_mul_right _ _ (pow_ne_zero E (by positivity))]
        · rw [Sc_eq, Nat.cast_sum, Finset.sum_div]
          refine Finset.sum_congr rfl fun s hs => ?_
          rw [Finset.mem_Ico] at hs
          rw [card_cBox (by omega) hπ hs.1 (by omega)
            (fun p hp => splitPairs_snd_ne_zero hp)]
          rw [Nat.cast_mul, Nat.cast_pow]
          obtain ⟨E, hE1, hE2⟩ : ∃ E, 4 * (M + 4) - (3 * s + 7) = E
              ∧ 4 * (M + 4) = E + (3 * s + 7) := ⟨_, rfl, by omega⟩
          rw [hE1, hE2, pow_add,
            mul_comm (((residueCard O : ℕ) : ℝ) ^ E)
              (((residueCard O : ℕ) : ℝ) ^ (3 * s + 7)),
            mul_div_mul_right _ _ (pow_ne_zero E (by positivity))]
      have hlim := (tendsto_geom_sum (q := ((residueCard O : ℕ) : ℝ)) hq2R
          ((((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)) 2 4 _
          tendsto_Vb_window).add
        (tendsto_geom_sum (q := ((residueCard O : ℕ) : ℝ)) hq2R
          ((Nat.card (digTriples (ResidueField O) (splitPairs (ResidueField O)))) : ℝ)
          1 7 _ tendsto_Sc_window)
      have hval : ((((Polynomial.X - 1) ^ 2 * Polynomial.X ^ 4 : Polynomial ℚ).eval
            ((residueCard O : ℕ) : ℚ)
          / (Polynomial.C 2 * ((Polynomial.X ^ 3 - 1) * Polynomial.X ^ 10)
              : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
          = (((residueCard O : ℕ) : ℝ) - 1) * (((residueCard O : ℕ) : ℝ) - 1)
              * ((residueCard O : ℕ) : ℝ) ^ 3
              / ((((residueCard O : ℕ) : ℝ) ^ 3 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (3 * 2 + 4))
            + ((Nat.card (digTriples (ResidueField O)
                (splitPairs (ResidueField O)))) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ 3
              / ((((residueCard O : ℕ) : ℝ) ^ 3 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (3 * 1 + 7)) := by
        rw [Rat.cast_div]
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C]
        push_cast
        rw [digTriples_split_val]
        have hq0R : ((residueCard O : ℕ) : ℝ) ≠ 0 := by
          intro h
          rw [h] at hq2R
          norm_num at hq2R
        have h3R : (((residueCard O : ℕ) : ℝ) ^ 3 - 1) ≠ 0 := by
          intro h
          have h2 := sub_eq_zero.1 h
          have : (8 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) ^ 3 := by
            calc (8 : ℝ) = 2 ^ 3 := by norm_num
              _ ≤ _ := by gcongr
          linarith
        field_simp
        ring
      rw [hval]
      exact hlim.congr (fun M => (hM M).symm)

/-- ★★ **The genre-(c)-irreducible limit** — THE UNCONDITIONAL INERT VALUE: value
`(q−1)²·q⁴ / (2(q³−1)·q¹⁰)` (equal to the splitTail depth-0 value — the split/inert
symmetry of the quadratic residual). -/
theorem zcURLim_e2Inert0Fam : ZcURLim e2Inert0Fam := by
  refine ⟨(Polynomial.X - 1) ^ 2 * Polynomial.X ^ 4,
    Polynomial.C 2 * ((Polynomial.X ^ 3 - 1) * Polynomial.X ^ 10), ?_, ?_⟩
  · refine mul_ne_zero (Polynomial.C_ne_zero.mpr two_ne_zero)
      (mul_ne_zero ?_ (pow_ne_zero _ Polynomial.X_ne_zero))
    intro h
    have h2 := congrArg (Polynomial.eval (0 : ℚ)) h
    simp at h2
  · intro O _ _ _ _ _
    have hq2 : 2 ≤ residueCard O := two_le_residueCard O
    have hqQ : (2 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) := by exact_mod_cast hq2
    have hqQ0 : ((residueCard O : ℕ) : ℚ) ≠ 0 := by linarith
    have h8 : (8 : ℚ) ≤ ((residueCard O : ℕ) : ℚ) ^ 3 := by
      calc (8 : ℚ) = 2 ^ 3 := by norm_num
        _ ≤ _ := by gcongr
    have hd3 : ((residueCard O : ℕ) : ℚ) ^ 3 - 1 ≠ 0 := by
      intro h
      have h2 := sub_eq_zero.1 h
      linarith
    refine ⟨?_, ?_⟩
    · rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_one]
      exact mul_ne_zero two_ne_zero (mul_ne_zero hd3 (pow_ne_zero _ hqQ0))
    · intro π hπ
      have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast hq2
      have hM : ∀ M, e2Inert0Fam O π M
          = ∑ s ∈ Finset.Ico 1 ((M + 4) / 2),
              ((Nat.card (digTriples (ResidueField O)
                  (irrPairs (ResidueField O)))) : ℝ)
                / ((residueCard O : ℕ) : ℝ) ^ (3 * s + 7) := by
        intro M
        show ((∑ s ∈ Sc (M + 4),
            Nat.card ((cBox π (M + 4) s (irrPairs (ResidueField O)))
              : Set (Coeff O 4 (M + 4)))) : ℝ)
            / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) = _
        rw [Sc_eq, Finset.sum_div]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [Finset.mem_Ico] at hs
        rw [card_cBox (by omega) hπ hs.1 (by omega)
          (fun p hp => irrPairs_snd_ne_zero hp)]
        rw [Nat.cast_mul, Nat.cast_pow]
        obtain ⟨E, hE1, hE2⟩ : ∃ E, 4 * (M + 4) - (3 * s + 7) = E
            ∧ 4 * (M + 4) = E + (3 * s + 7) := ⟨_, rfl, by omega⟩
        rw [hE1, hE2, pow_add,
          mul_comm (((residueCard O : ℕ) : ℝ) ^ E)
            (((residueCard O : ℕ) : ℝ) ^ (3 * s + 7)),
          mul_div_mul_right _ _ (pow_ne_zero E (by positivity))]
      have hlim := tendsto_geom_sum (q := ((residueCard O : ℕ) : ℝ)) hq2R
        ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ)
        1 7 _ tendsto_Sc_window
      have hval : ((((Polynomial.X - 1) ^ 2 * Polynomial.X ^ 4 : Polynomial ℚ).eval
            ((residueCard O : ℕ) : ℚ)
          / (Polynomial.C 2 * ((Polynomial.X ^ 3 - 1) * Polynomial.X ^ 10)
              : Polynomial ℚ).eval ((residueCard O : ℕ) : ℚ) : ℚ) : ℝ)
          = ((Nat.card (digTriples (ResidueField O) (irrPairs (ResidueField O)))) : ℝ)
              * ((residueCard O : ℕ) : ℝ) ^ 3
              / ((((residueCard O : ℕ) : ℝ) ^ 3 - 1)
                * ((residueCard O : ℕ) : ℝ) ^ (3 * 1 + 7)) := by
        rw [Rat.cast_div]
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C]
        push_cast
        rw [digTriples_irr_val]
        have hq0R : ((residueCard O : ℕ) : ℝ) ≠ 0 := by
          intro h
          rw [h] at hq2R
          norm_num at hq2R
        have h3R : (((residueCard O : ℕ) : ℝ) ^ 3 - 1) ≠ 0 := by
          intro h
          have h2 := sub_eq_zero.1 h
          have : (8 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) ^ 3 := by
            calc (8 : ℝ) = 2 ^ 3 := by norm_num
              _ ≤ _ := by gcongr
          linarith
        field_simp
      rw [hval]
      exact hlim.congr (fun M => (hM M).symm)

/-! ### §7d — the boundary squeeze data -/

section Boundary

private theorem e2BdDecFam_nonneg (σ : FactorizationType) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ (π : O) (M : ℕ), 0 ≤ e2BdDecFam σ O π M := by
  intro O _ _ _ _ _ π M
  show (0 : ℝ) ≤ (Nat.card ((decidedSet O 4 σ (M + 4) ∩ bdBox O (M + 4))
      : Set (Coeff O 4 (M + 4))) : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  positivity

private theorem e2BdDecFam_le (σ : FactorizationType) :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ (π : O) (M : ℕ),
        e2BdDecFam σ O π M ≤ (1 / ((residueCard O : ℕ) : ℝ)) ^ (M + 4) := by
  intro O _ _ _ _ _ π M
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hqR : (0 : ℝ) < ((residueCard O : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast hq2
    linarith
  show (Nat.card ((decidedSet O 4 σ (M + 4) ∩ bdBox O (M + 4))
      : Set (Coeff O 4 (M + 4))) : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) ≤ _
  have h1 : Nat.card ((decidedSet O 4 σ (M + 4) ∩ bdBox O (M + 4))
      : Set (Coeff O 4 (M + 4))) ≤ residueCard O ^ (3 * (M + 4)) :=
    le_trans (Nat.card_mono (Set.toFinite _) Set.inter_subset_right)
      (card_bdBox_le (by omega))
  calc (Nat.card ((decidedSet O 4 σ (M + 4) ∩ bdBox O (M + 4))
        : Set (Coeff O 4 (M + 4))) : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
      ≤ ((residueCard O ^ (3 * (M + 4)) : ℕ) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)) := by
        gcongr
    _ = (1 / ((residueCard O : ℕ) : ℝ)) ^ (M + 4) := by
        rw [Nat.cast_pow, one_div_pow,
          show 4 * (M + 4) = 3 * (M + 4) + (M + 4) from by ring, pow_add,
          div_eq_div_iff (by positivity) (by positivity), one_mul]

private theorem tendsto_bd_bound :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      Filter.Tendsto (fun M : ℕ => (1 / ((residueCard O : ℕ) : ℝ)) ^ (M + 4))
        Filter.atTop (nhds 0) := by
  intro O _ _ _ _ _
  have hq2 : 2 ≤ residueCard O := two_le_residueCard O
  have hq2R : (2 : ℝ) ≤ ((residueCard O : ℕ) : ℝ) := by exact_mod_cast hq2
  have h0 : (0 : ℝ) ≤ 1 / ((residueCard O : ℕ) : ℝ) := by positivity
  have h1 : 1 / ((residueCard O : ℕ) : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp
    (Filter.tendsto_add_atTop_nat 4)

end Boundary

/-! ### §7e — the decompositions -/

section Decomp

private theorem e2DecFam_decomp_ramPair :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ π : O, Irreducible π → ∀ M,
        e2DecFam ramPairType O π M
          = (e2Ram0Fam O π M + e2DdDecFam ramPairType O π M)
            + e2BdDecFam ramPairType O π M := by
  intro O _ _ _ _ _ π hπ M
  have hnum : (Nat.card ((decidedSet O 4 ramPairType (M + 4) ∩ e2Box O (M + 4))
        : Set (Coeff O 4 (M + 4))) : ℝ)
      = (∑ t ∈ Ta (M + 4), (Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4))) : ℝ))
        + ((Nat.card ((decidedSet O 4 ramPairType (M + 4) ∩ e2DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ)
          + (Nat.card ((decidedSet O 4 ramPairType (M + 4) ∩ bdBox O (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ)) := by
    exact_mod_cast card_decided_ramPair (by omega) hπ
  show (Nat.card ((decidedSet O 4 ramPairType (M + 4) ∩ e2Box O (M + 4))
      : Set (Coeff O 4 (M + 4))) : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
    = ((∑ t ∈ Ta (M + 4), (Nat.card (aBox O (M + 4) t : Set (Coeff O 4 (M + 4))) : ℝ))
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
        + (Nat.card ((decidedSet O 4 ramPairType (M + 4) ∩ e2DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)))
      + (Nat.card ((decidedSet O 4 ramPairType (M + 4) ∩ bdBox O (M + 4))
          : Set (Coeff O 4 (M + 4))) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  rw [← add_div, ← add_div, hnum]
  ring

private theorem e2DecFam_decomp_splitTail :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ π : O, Irreducible π → ∀ M,
        e2DecFam splitTailType O π M
          = (e2Split0Fam O π M + e2DdDecFam splitTailType O π M)
            + e2BdDecFam splitTailType O π M := by
  intro O _ _ _ _ _ π hπ M
  have hnum : (Nat.card ((decidedSet O 4 splitTailType (M + 4) ∩ e2Box O (M + 4))
        : Set (Coeff O 4 (M + 4))) : ℝ)
      = ((((∑ v ∈ Vb (M + 4), Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4)))) : ℕ) : ℝ)
          + (((∑ s ∈ Sc (M + 4),
              Nat.card ((cBox π (M + 4) s (splitPairs (ResidueField O)))
                : Set (Coeff O 4 (M + 4)))) : ℕ) : ℝ))
        + ((Nat.card ((decidedSet O 4 splitTailType (M + 4) ∩ e2DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ)
          + (Nat.card ((decidedSet O 4 splitTailType (M + 4) ∩ bdBox O (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ)) := by
    exact_mod_cast card_decided_splitTail (by omega) hπ
  show (Nat.card ((decidedSet O 4 splitTailType (M + 4) ∩ e2Box O (M + 4))
      : Set (Coeff O 4 (M + 4))) : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
    = (((((∑ v ∈ Vb (M + 4), Nat.card (bBox O (M + 4) v : Set (Coeff O 4 (M + 4)))) : ℕ) : ℝ)
            + (((∑ s ∈ Sc (M + 4),
                Nat.card ((cBox π (M + 4) s (splitPairs (ResidueField O)))
                  : Set (Coeff O 4 (M + 4)))) : ℕ) : ℝ))
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
        + (Nat.card ((decidedSet O 4 splitTailType (M + 4) ∩ e2DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)))
      + (Nat.card ((decidedSet O 4 splitTailType (M + 4) ∩ bdBox O (M + 4))
          : Set (Coeff O 4 (M + 4))) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  rw [← add_div, ← add_div, hnum]
  ring

private theorem e2DecFam_decomp_inertTail :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
      ∀ π : O, Irreducible π → ∀ M,
        e2DecFam inertTailType O π M
          = (e2Inert0Fam O π M + e2DdDecFam inertTailType O π M)
            + e2BdDecFam inertTailType O π M := by
  intro O _ _ _ _ _ π hπ M
  have hnum : (Nat.card ((decidedSet O 4 inertTailType (M + 4) ∩ e2Box O (M + 4))
        : Set (Coeff O 4 (M + 4))) : ℝ)
      = (∑ s ∈ Sc (M + 4),
            (Nat.card ((cBox π (M + 4) s (irrPairs (ResidueField O)))
              : Set (Coeff O 4 (M + 4))) : ℝ))
        + ((Nat.card ((decidedSet O 4 inertTailType (M + 4) ∩ e2DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ)
          + (Nat.card ((decidedSet O 4 inertTailType (M + 4) ∩ bdBox O (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ)) := by
    exact_mod_cast card_decided_inertTail (by omega) hπ
  show (Nat.card ((decidedSet O 4 inertTailType (M + 4) ∩ e2Box O (M + 4))
      : Set (Coeff O 4 (M + 4))) : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
    = ((∑ s ∈ Sc (M + 4),
            (Nat.card ((cBox π (M + 4) s (irrPairs (ResidueField O)))
              : Set (Coeff O 4 (M + 4))) : ℝ))
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
        + (Nat.card ((decidedSet O 4 inertTailType (M + 4) ∩ e2DdBox π (M + 4))
            : Set (Coeff O 4 (M + 4))) : ℝ)
          / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4)))
      + (Nat.card ((decidedSet O 4 inertTailType (M + 4) ∩ bdBox O (M + 4))
          : Set (Coeff O 4 (M + 4))) : ℝ)
        / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  rw [← add_div, ← add_div, hnum]
  ring

end Decomp

/-! ### §8 — ★★★ THE THREE E2 LIMITS on the named dd premise, and the `∀ σ` closure -/

section Main

/-- ★★★ **The ramPair E2 limit** — on the named dd-recursion premise ALONE. -/
theorem zcURLim_e2DecFam_ramPair (h : ZcURLim (e2DdDecFam ramPairType)) :
    ZcURLim (e2DecFam ramPairType) := by
  refine ZcURLim.sandwich (zcURLim_e2Ram0Fam.add h)
    (E := fun O _ _ _ _ _ _ M => (1 / ((residueCard O : ℕ) : ℝ)) ^ (M + 4))
    (fun O _ _ _ _ _ π hπ => tendsto_bd_bound O) ?_ ?_
  · intro O _ _ _ _ _ π hπ M
    rw [e2DecFam_decomp_ramPair O π hπ M]
    exact le_add_of_nonneg_right (e2BdDecFam_nonneg _ O π M)
  · intro O _ _ _ _ _ π hπ M
    rw [e2DecFam_decomp_ramPair O π hπ M]
    exact add_le_add_right (e2BdDecFam_le _ O π M) _

/-- ★★★ **The splitTail E2 limit** — on the named dd-recursion premise ALONE. -/
theorem zcURLim_e2DecFam_splitTail (h : ZcURLim (e2DdDecFam splitTailType)) :
    ZcURLim (e2DecFam splitTailType) := by
  refine ZcURLim.sandwich (zcURLim_e2Split0Fam.add h)
    (E := fun O _ _ _ _ _ _ M => (1 / ((residueCard O : ℕ) : ℝ)) ^ (M + 4))
    (fun O _ _ _ _ _ π hπ => tendsto_bd_bound O) ?_ ?_
  · intro O _ _ _ _ _ π hπ M
    rw [e2DecFam_decomp_splitTail O π hπ M]
    exact le_add_of_nonneg_right (e2BdDecFam_nonneg _ O π M)
  · intro O _ _ _ _ _ π hπ M
    rw [e2DecFam_decomp_splitTail O π hπ M]
    exact add_le_add_right (e2BdDecFam_le _ O π M) _

/-- ★★★ **The inertTail E2 limit** — on the named dd-recursion premise ALONE. -/
theorem zcURLim_e2DecFam_inertTail (h : ZcURLim (e2DdDecFam inertTailType)) :
    ZcURLim (e2DecFam inertTailType) := by
  refine ZcURLim.sandwich (zcURLim_e2Inert0Fam.add h)
    (E := fun O _ _ _ _ _ _ M => (1 / ((residueCard O : ℕ) : ℝ)) ^ (M + 4))
    (fun O _ _ _ _ _ π hπ => tendsto_bd_bound O) ?_ ?_
  · intro O _ _ _ _ _ π hπ M
    rw [e2DecFam_decomp_inertTail O π hπ M]
    exact le_add_of_nonneg_right (e2BdDecFam_nonneg _ O π M)
  · intro O _ _ _ _ _ π hπ M
    rw [e2DecFam_decomp_inertTail O π hπ M]
    exact add_le_add_right (e2BdDecFam_le _ O π M) _

/-- ★★ **Every OFF-SHAPE type closes at `0` UNCONDITIONALLY** (the shape pin). -/
theorem zcURLim_e2DecFam_of_shape {σ : FactorizationType} (h1 : σ ≠ ramPairType)
    (h2 : σ ≠ splitTailType) (h3 : σ ≠ inertTailType) :
    ZcURLim (e2DecFam σ) := by
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  show (0 : ℝ) = (Nat.card ((decidedSet O 4 σ (M + 4) ∩ e2Box O (M + 4))
      : Set (Coeff O 4 (M + 4))) : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (4 * (M + 4))
  rw [decided_inter_e2_eq_empty_of_shape (by omega) h1 h2 h3]
  simp

/-- ★★★ **THE FULL `∀ σ` E2 CLOSURE** — every `e2DecFam` limit, on exactly the THREE
named dd-recursion terms (ASM scoreboard row 7, discharged to depth ≥ 1). -/
theorem zcURLim_e2DecFam_all (h1 : ZcURLim (e2DdDecFam ramPairType))
    (h2 : ZcURLim (e2DdDecFam splitTailType))
    (h3 : ZcURLim (e2DdDecFam inertTailType)) :
    ∀ σ : FactorizationType, ZcURLim (e2DecFam σ) := by
  intro σ
  by_cases hr : σ = ramPairType
  · subst hr
    exact zcURLim_e2DecFam_ramPair h1
  by_cases hs : σ = splitTailType
  · subst hs
    exact zcURLim_e2DecFam_splitTail h2
  by_cases hi : σ = inertTailType
  · subst hi
    exact zcURLim_e2DecFam_inertTail h3
  exact zcURLim_e2DecFam_of_shape hr hs hi

end Main

end Limits

/-! ## §9 — the census rows, re-fired -/

section Rows

open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG25 (UnramifiedBlockBridge)

/-- ★★ **The `{(2,1),(2,1)}` row**: two named recursion terms (E1-dd order-2, E2-dd). -/
theorem coneRemainderLaw_four_ramPair_of_dd
    (h2 : ZcURLim (e1DdDecFam ramPairType))
    (h3 : ZcURLim (e2DdDecFam ramPairType)) :
    ConeRemainderLaw 4 ramPairType :=
  Uniformity.Density.IFCG36.coneRemainderLaw_four_ramPair h2
    (zcURLim_e2DecFam_ramPair h3)

/-- ★★ **The `{(1,1),(1,1),(2,1)}` row**: ONE named recursion term (E2-dd). -/
theorem coneRemainderLaw_four_splitTail_of_dd
    (h : ZcURLim (e2DdDecFam splitTailType)) :
    ConeRemainderLaw 4 splitTailType := by
  refine coneRemainderLaw_four_of_odd_member ?_ ?_ (zcURLim_e2DecFam_splitTail h)
  · exact fun he => absurd (congrArg FactorizationType.data he) (by decide)
  · exact ⟨(1, 1), by decide, by decide⟩

/-- ★★ **The `{(1,2),(2,1)}` row**: ONE named recursion term (E2-dd). -/
theorem coneRemainderLaw_four_inertTail_of_dd
    (h : ZcURLim (e2DdDecFam inertTailType)) :
    ConeRemainderLaw 4 inertTailType := by
  refine coneRemainderLaw_four_of_odd_member ?_ ?_ (zcURLim_e2DecFam_inertTail h)
  · exact fun he => absurd (congrArg FactorizationType.data he) (by decide)
  · exact ⟨(1, 2), by decide, by decide⟩

/-- ★★★ **THE CENSUS FRONT, REWIRED** (the scoreboard delta): IFCG36's `hE2 : ∀ σ`
premise is DISCHARGED to the three named E2 dd-recursion terms — the all-degree decided
slice now rests on {`E1IrrLeafDecision`, `∀σ e1Dd`, THREE `e2Dd` terms, the `e ≥ 5`
laws, the block bridges}. -/
theorem decidedSliceAt_all_of_dd_limits (hL : E1IrrLeafDecision)
    (hDd : ∀ σ : FactorizationType, ZcURLim (e1DdDecFam σ))
    (hE2a : ZcURLim (e2DdDecFam ramPairType))
    (hE2b : ZcURLim (e2DdDecFam splitTailType))
    (hE2c : ZcURLim (e2DdDecFam inertTailType))
    (hR : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ConeRemainderLaw e σ)
    (hBr : ∀ δ e : ℕ, 2 ≤ δ → 2 ≤ e → UnramifiedBlockBridge δ e) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG36.decidedSliceAt_all_of_recursion_limits hL hDd
    (zcURLim_e2DecFam_all hE2a hE2b hE2c) hR hBr

end Rows

end Uniformity.Density.IFCG53

end

/-! ## AXCHECK FOOTER — the field-side trichotomy, the counting layer, the digit-triple
engine, and the limit machinery expect Lean core `{propext, Classical.choice,
Quot.sound}`; the decisions, partition identities, counts-of-decided, the three E2
limits, the rows, and the front expect Lean core PLUS exactly the owner-signed gate-(b)
cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42), inherited through
IFCG26's two-point-side peel and IFCG34/36's landed counts.  The C.33 cites must NOT
occur. -/

#print axioms Uniformity.Density.IFCG53.pair_trichotomy
#print axioms Uniformity.Density.IFCG53.disjoint_splitPairs_irrPairs
#print axioms Uniformity.Density.IFCG53.disjoint_splitPairs_ddPairs
#print axioms Uniformity.Density.IFCG53.disjoint_irrPairs_ddPairs
#print axioms Uniformity.Density.IFCG53.decidedAt_aBox
#print axioms Uniformity.Density.IFCG53.decidedAt_bBox
#print axioms Uniformity.Density.IFCG53.decidedAt_cIrrBox
#print axioms Uniformity.Density.IFCG53.decidedAt_cSplitBox
#print axioms Uniformity.Density.IFCG53.typeOf_e2_mem
#print axioms Uniformity.Density.IFCG53.decided_inter_e2_eq_empty_of_shape
#print axioms Uniformity.Density.IFCG53.mem_genre_cases
#print axioms Uniformity.Density.IFCG53.decided_ramPair_inter_e2Box
#print axioms Uniformity.Density.IFCG53.decided_splitTail_inter_e2Box
#print axioms Uniformity.Density.IFCG53.decided_inertTail_inter_e2Box
#print axioms Uniformity.Density.IFCG53.card_decided_ramPair
#print axioms Uniformity.Density.IFCG53.card_decided_splitTail
#print axioms Uniformity.Density.IFCG53.card_decided_inertTail
#print axioms Uniformity.Density.IFCG53.card_aBox
#print axioms Uniformity.Density.IFCG53.card_bBox
#print axioms Uniformity.Density.IFCG53.card_bdBox_le
#print axioms Uniformity.Density.IFCG53.card_digTriples
#print axioms Uniformity.Density.IFCG53.card_cBox
#print axioms Uniformity.Density.IFCG53.ZcURLim.sandwich
#print axioms Uniformity.Density.IFCG53.tendsto_geom_sum
#print axioms Uniformity.Density.IFCG53.zcURLim_e2Ram0Fam
#print axioms Uniformity.Density.IFCG53.zcURLim_e2Split0Fam
#print axioms Uniformity.Density.IFCG53.zcURLim_e2Inert0Fam
#print axioms Uniformity.Density.IFCG53.zcURLim_e2DecFam_ramPair
#print axioms Uniformity.Density.IFCG53.zcURLim_e2DecFam_splitTail
#print axioms Uniformity.Density.IFCG53.zcURLim_e2DecFam_inertTail
#print axioms Uniformity.Density.IFCG53.zcURLim_e2DecFam_of_shape
#print axioms Uniformity.Density.IFCG53.zcURLim_e2DecFam_all
#print axioms Uniformity.Density.IFCG53.coneRemainderLaw_four_ramPair_of_dd
#print axioms Uniformity.Density.IFCG53.coneRemainderLaw_four_splitTail_of_dd
#print axioms Uniformity.Density.IFCG53.coneRemainderLaw_four_inertTail_of_dd
#print axioms Uniformity.Density.IFCG53.decidedSliceAt_all_of_dd_limits
