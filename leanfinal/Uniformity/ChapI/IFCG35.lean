/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapB.B30
import Uniformity.ChapB.B58
import Uniformity.ChapB.B61
import Uniformity.ChapI.IFCG17
import Uniformity.ChapI.IFCG28
import Uniformity.ChapI.IFCG32
import Uniformity.ChapI.IFCG33

/-!
# Uniformity.ChapI.IFCG35 — [RECUR 2026-08-30] the uniform remainder recursion:
the residual trichotomy of the cone-remainder carrier, the leaf laws, and the
census front re-based on the three sector laws

Stage RECUR of the cone census (design record `runs/wave-c/verdict_RECUR.md`).  After
UZL (`IFCG33`) the census front is EXACTLY `ConeRemainderLaw e σ` at `e ≥ 5` for the
genuinely ramified types, plus the five `e = 4` even-ramification types (another
unit's).  This file organizes the ramified remainder at EVERY mass by the recursion's
trichotomy and fires everything the landed engines reach:

* **§1 the leaf laws.**  `ResidualLeafLaw e' d` — the residual-irreducible leaf at
  parameters `(e', d)`: a monic x-pure block of slope `u/e'` whose side residual is
  IRREDUCIBLE of degree `d` has type `⟨{(e', d)}⟩`.  The `d = 1` member is PROVED
  outright (`residualLeafLaw_one`, B.61 with a trivial box — CN2's Eisenstein genre);
  every `d` follows from the ONE named open supply `ResidualInertiaSupply` (B.63's
  B-BOX-1 perimeter clause at the x-frame: the residual field of an irreducible side
  residual embeds into every factor's residue extension — IFCG32's norm machinery is
  the natural discharge route).
* **§2 the canonical face and the class residual.**  Every shallow stratum class has a
  UNIQUE minimal-slope last-edge face `MinFaceAt c h e'` (UZL's construction,
  re-derived with the attainment at the monic point and slope-minimality exported, and
  the new uniqueness theorem `minFaceAt_unique`), and a well-defined residual
  polynomial `classResidualPoly π c h e'` (lift-independent by WFR §3's transport,
  `classResidualPoly_eq`).
* **§2c the split dichotomy.**  Over any field, a nonconstant polynomial that is
  neither irreducible nor a proper prime power splits into two coprime monic
  nonconstant factors (`exists_coprime_split_of_not_primary`) — the exact input shape
  of XHS's `wideFace_refinement_of_stratum`.
* **§3 ★★ THE TRICHOTOMY PARTITION.**  The remainder carrier partitions EXACTLY into
  the three recursion sectors, by the factorization pattern of the minimal-face class
  residual: `leafSector` (residual irreducible — the leaf), `powerSector` (a proper
  power of one irreducible — the fractional-recentring step's territory), and
  `splitSector` (coprime-reducible — the smaller-mass convolution's territory).
  `coneRemainderCount = split + power + leaf`, exact at every level, every mass,
  every σ, every uniformizer.
* **§4 ★★ the sector laws.**  `SplitSectorLaw/PowerSectorLaw/LeafSectorLaw m σ` — the
  three named remainder residues — and the assembly
  `coneRemainderLaw_of_sectorLaws : the three laws ⟹ ConeRemainderLaw m σ`.
* **§5 ★ the spanning leaf decisions.**  `decidedAt_of_spanning_leaf`: a class whose
  face spans `[0, m]` with irreducible class residual of degree `d` is DECIDED
  `⟨{(e', d)}⟩` (conditional exactly on `ResidualLeafLaw e' d`); at `d = 1` this is
  UNCONDITIONAL and recovers CN2's `decidedAt_of_eisenstein_face` through the leaf
  engine (`decidedAt_of_spanning_eisenstein`).
* **§6 ★★★ the census front through the trichotomy**
  (`decidedSliceAt_all_of_sectorLaws`): the all-degree decided slice rests on EXACTLY
  the three sector laws at `(e ≥ 5, σ ramified)` — each consumed with the smaller-mass
  decided value laws as premises, the recursion's own descent shape — plus the five
  `e = 4` even-ramification laws.  The bridge family is GONE (IFCG32).

## The recursion record (what survives after this file)

`∀ n, DecidedSliceAt n` rests on exactly:
1. `SplitSectorLaw e σ` at `e ≥ 5`, σ ramified (under the `< e` value laws) — the
   convolution to strictly smaller masses (XHS §4 refines; IFCG17's `stratDecCount_mul`
   is the landed counting genre);
2. `PowerSectorLaw e σ` at `e ≥ 5`, σ ramified (same supply) — the fractional
   recentring/tower step (IFCG20's copy machinery at fractional centres, C136's tower);
3. `LeafSectorLaw e σ` at `e ≥ 5`, σ ramified (same supply) — the leaf census; its
   DECISION content is closed here modulo `ResidualInertiaSupply` (`d ≥ 2`; `d = 1`
   unconditional);
4. the five `e = 4` even-ramification `ConeRemainderLaw`s (ER4's unit);
5. `ResidualInertiaSupply` — the one named open leaf-decision leg.

## Axiom fence

§§1–5 consume at most the owner-signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42), inherited through the
landed IFCG26/IFCG28 transports; the partition §3 and the arithmetic §2 are Lean-core.
§6 inherits IFCG31/IFCG33's B.42 cite.  The C.33 cites must NOT occur.  Zero sorries
at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG35

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply classNPSupport_le le_classNPSupport)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero shallowSet mem_stratum_X_pow_iff
  pureFaceSet coneRemainderCount ConeRemainderLaw ZeroConeClause
  zeroConeClause_of_remainderLaw npHeight_coe)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains fracFaceForcesRam_of_stratum)
open Uniformity.Density.IFCG28 (onSide_monicPoly_iff sideSet_monicPoly_eq
  sideMin_monicPoly_eq sideMax_monicPoly_eq resPoly_monicPoly_eq classSideSet)
open Uniformity.Density.IFCG23 (isPure_monicPoly_of_face npHgt_monicPoly_eq
  npHgt_monicPoly_top)

attribute [local instance] Classical.propDecidable

/-! ## §0 — supply -/

section Supply

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private theorem isKey_X : IsKey (Polynomial.X : Polynomial O) where
  monic := Polynomial.monic_X
  pos := by simp
  irred := by rw [Polynomial.map_X]; exact Polynomial.irreducible_X

/-- B83Kit's membership unfolding for the Classical `sideSet` filter (private copy). -/
private theorem mem_sideSet_iff' {φ f : Polynomial O} {u ℓ j : ℕ} :
    j ∈ sideSet φ f u ℓ ↔ (j < f.natDegree + 1 ∧ OnSide φ f u ℓ j) := by
  classical
  constructor
  · intro hj
    have hj' : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) := hj
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hj'
    exact ⟨Finset.mem_range.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    have : j ∈ Finset.filter (OnSide φ f u ℓ) (Finset.range (f.natDegree + 1)) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 h1, h2⟩
    exact this

end Supply

/-! ## §1 — the leaf laws: the residual-irreducible leaf at `(e', d)` -/

section LeafLaw

/-- **THE ONE NAMED OPEN LEAF LEG — the x-frame residual-inertia supply** (B.63's
B-BOX-1/perimeter clause at `φ = X`): if a monic x-pure block's side residual is
IRREDUCIBLE, its degree divides the inertia degree of every monic irreducible factor
of the block.  This is the classical "residual field embeds into the factor's residue
extension"; IFCG32's norm-transport machinery is the natural discharge route.  At
residual degree `1` the statement is TRIVIAL (and the leaf law below is proved
outright). -/
def ResidualInertiaSupply : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ π : O, Irreducible π →
  ∀ u ℓ : ℕ, 0 < u → 0 < ℓ → Nat.Coprime u ℓ →
  ∀ g : Polynomial O, g.Monic → IsPure X g u ℓ →
  ∀ (hne : (sideSet X g u ℓ).Nonempty) (H₀ : ℕ),
    npHgt X g (sideMin X g u ℓ hne) = (H₀ : ℕ∞) →
    Irreducible (resPoly π X g u ℓ hne H₀) →
    ∀ g' ∈ monicFactors g, sideDeg X g u ℓ hne ∣ inertiaDegOf g'

/-- **THE RESIDUAL-IRREDUCIBLE LEAF LAW at parameters `(e', d)`** — the recursion's
leaf node: a monic x-pure block of slope `u/e'` (`u ≥ 1`, coprime), side residual
degree `d`, residual pin `ḡ = X̄^(e'·d)`, whose side residual polynomial is
IRREDUCIBLE, has type EXACTLY `⟨{(e', d)}⟩`. -/
def ResidualLeafLaw (e' d : ℕ) : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)],
  ∀ π : O, Irreducible π →
  ∀ u : ℕ, 0 < u → Nat.Coprime u e' →
  ∀ g : Polynomial O, g.Monic → IsPure X g u e' →
  ∀ hne : (sideSet X g u e').Nonempty,
    sideDeg X g u e' hne = d →
    g.map (IsLocalRing.residue O) = X ^ (e' * d) →
  ∀ H₀ : ℕ, npHgt X g (sideMin X g u e' hne) = (H₀ : ℕ∞) →
    Irreducible (resPoly π X g u e' hne H₀) →
    typeOf g = ⟨{(e', d)}⟩

/-- ★ **The `d = 1` leaf, PROVED** (CN2's Eisenstein genre at the block level): B.61
with the box supply trivial. -/
theorem residualLeafLaw_one {e' : ℕ} (he' : 0 < e') : ResidualLeafLaw e' 1 := by
  intro O _ _ _ _ _ π hπ u hu hcop g hg hpure hne hsd hres H₀ hH _hirr
  have hbox : ∀ g' ∈ monicFactors g,
      (X : Polynomial O).natDegree * sideDeg X g u e' hne ∣ inertiaDegOf g' := by
    intro g' _
    rw [Polynomial.natDegree_X, one_mul, hsd]
    exact one_dvd _
  have hres' : g.map (IsLocalRing.residue O)
      = ((X : Polynomial O).map (IsLocalRing.residue O))
          ^ (e' * sideDeg X g u e' hne) := by
    rw [Polynomial.map_X, hsd]
    exact hres
  have hty := typeOf_leaf_of_resDeg_lower_bound hπ isKey_X hu he' hcop hg hpure hne
    (by omega : 0 < sideDeg X g u e' hne) hres' hbox
  rw [hty, Polynomial.natDegree_X, one_mul, hsd]

/-- ★ **The general leaf from the one named supply**: B.61's box discharged by
`ResidualInertiaSupply`. -/
theorem residualLeafLaw_of_supply (hS : ResidualInertiaSupply) {e' d : ℕ}
    (he' : 0 < e') (hd : 0 < d) : ResidualLeafLaw e' d := by
  intro O _ _ _ _ _ π hπ u hu hcop g hg hpure hne hsd hres H₀ hH hirr
  have hbox : ∀ g' ∈ monicFactors g,
      (X : Polynomial O).natDegree * sideDeg X g u e' hne ∣ inertiaDegOf g' := by
    intro g' hg'
    rw [Polynomial.natDegree_X, one_mul]
    exact hS O π hπ u e' hu he' hcop g hg hpure hne H₀ hH hirr g' hg'
  have hres' : g.map (IsLocalRing.residue O)
      = ((X : Polynomial O).map (IsLocalRing.residue O))
          ^ (e' * sideDeg X g u e' hne) := by
    rw [Polynomial.map_X, hsd]
    exact hres
  have hty := typeOf_leaf_of_resDeg_lower_bound hπ isKey_X hu he' hcop hg hpure hne
    (by omega : 0 < sideDeg X g u e' hne) hres' hbox
  rw [hty, Polynomial.natDegree_X, one_mul, hsd]

end LeafLaw

/-! ## §2 — the canonical minimal-slope face and the class residual -/

section MinFace

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

/-- **The minimal-slope last-edge face**: the fractional face `h/e'` (`1 ≤ h < e'`,
coprime) attained at the monic point `m`, visible, with a genuine second attainment
(`ClassNPFace`).  On the shallow stratum this is UZL's last hull edge; it is UNIQUE
(`minFaceAt_unique`), so it canonically indexes the carrier's trichotomy. -/
def MinFaceAt {m K : ℕ} (c : Coeff O m K) (h e' : ℕ) : Prop :=
  1 ≤ h ∧ h < e' ∧ Nat.Coprime h e' ∧ ClassNPFace c h e'
    ∧ NPAttains c h e' m ∧ NPVisibleAt c h e'

/-- The support of a minimal face is `h·m` (the monic point is attained). -/
theorem minFaceAt_support {m K : ℕ} {c : Coeff O m K} {h e' : ℕ}
    (hF : MinFaceAt c h e') : classNPSupport c h e' = h * m := by
  have h2 := hF.2.2.2.2.1.2
  have hnpm : npHeight c m = 0 := by
    unfold npHeight
    rw [dif_neg (lt_irrefl m)]
  rw [hnpm, Nat.mul_zero, Nat.zero_add] at h2
  exact h2.symm

/-- **Slope minimality**: the minimal face's slope bounds every height from below,
`h·(m − i) ≤ e'·v_i`. -/
theorem minFaceAt_min {m K : ℕ} {c : Coeff O m K} {h e' : ℕ}
    (hF : MinFaceAt c h e') (i : Fin m) :
    h * (m - (i : ℕ)) ≤ e' * resOrd (c i) := by
  have hsup := minFaceAt_support hF
  have hle := classNPSupport_le_apply c h e' (le_of_lt i.isLt)
  have hnp : npHeight c (i : ℕ) = resOrd (c i) := by
    have h5 := npHeight_coe c i
    simpa using h5
  rw [hnp, hsup] at hle
  have hsplit : h * (m - (i : ℕ)) + h * (i : ℕ) = h * m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt i.isLt)]
  rw [← hsplit] at hle
  exact Nat.le_of_add_le_add_right hle

/-- Some abscissa `i < m` attains the minimal face exactly: `e'·v_i = h·(m − i)`. -/
theorem minFaceAt_attained_lt {m K : ℕ} {c : Coeff O m K} {h e' : ℕ}
    (hF : MinFaceAt c h e') : ∃ i : Fin m, e' * resOrd (c i) = h * (m - (i : ℕ)) := by
  obtain ⟨i, j, hij, hAi, hAj⟩ := hF.2.2.2.1
  have hsup := minFaceAt_support hF
  have hilt : i < m := lt_of_lt_of_le hij hAj.1
  have h2 := hAi.2
  have hnp : npHeight c i = resOrd (c ⟨i, hilt⟩) := by
    have h5 := npHeight_coe c ⟨i, hilt⟩
    simpa using h5
  rw [hnp, hsup] at h2
  refine ⟨⟨i, hilt⟩, ?_⟩
  have hsplit : h * (m - i) + h * i = h * m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hilt)]
  have h3 := h2.trans hsplit.symm
  exact Nat.add_right_cancel h3

/-- ★ **Existence** (UZL's last-hull-edge construction, re-derived with the monic-point
attainment exported): every shallow stratum class carries a minimal-slope face. -/
theorem exists_minFaceAt_of_shallow {m K : ℕ} (hmK : m ≤ K) {c : Coeff O m K}
    (hstr : ∀ i : Fin m, 1 ≤ resOrd (c i)) (hsh : c ∈ shallowSet O m K) :
    ∃ h e' : ℕ, MinFaceAt c h e' := by
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
  exact ⟨h, e', hh1, hhe, hcop, ⟨(j : ℕ), m, hjlt, hAj, hAm⟩, hAm, hvisi⟩

/-- ★ **Uniqueness**: the minimal-slope face data `(h, e')` is a class invariant — two
minimal faces agree.  (The slope is THE minimum of the last-edge slopes, and lowest
terms are unique.) -/
theorem minFaceAt_unique {m K : ℕ} {c : Coeff O m K} {h₁ e₁ h₂ e₂ : ℕ}
    (hF₁ : MinFaceAt c h₁ e₁) (hF₂ : MinFaceAt c h₂ e₂) : h₁ = h₂ ∧ e₁ = e₂ := by
  -- the cross bound: face₁'s exact attained point against face₂'s minimality
  have key : ∀ {a b a' b' : ℕ}, MinFaceAt c a b → MinFaceAt c a' b' → b * a' ≤ b' * a := by
    intro a b a' b' hFa hFb
    obtain ⟨i, hi⟩ := minFaceAt_attained_lt hFa
    have h2 := minFaceAt_min hFb i
    have hmi : 0 < m - (i : ℕ) := by
      have := i.isLt
      omega
    have h3 : b * (a' * (m - (i : ℕ))) ≤ b * (b' * resOrd (c i)) :=
      Nat.mul_le_mul (le_refl b) h2
    have h4 : b * (b' * resOrd (c i)) = (b' * a) * (m - (i : ℕ)) := by
      calc b * (b' * resOrd (c i)) = b' * (b * resOrd (c i)) := by ring
        _ = b' * (a * (m - (i : ℕ))) := by rw [hi]
        _ = (b' * a) * (m - (i : ℕ)) := by ring
    have h5 : (b * a') * (m - (i : ℕ)) ≤ (b' * a) * (m - (i : ℕ)) := by
      calc (b * a') * (m - (i : ℕ)) = b * (a' * (m - (i : ℕ))) := by ring
        _ ≤ b * (b' * resOrd (c i)) := h3
        _ = (b' * a) * (m - (i : ℕ)) := h4
    have h6 : (m - (i : ℕ)) * (b * a') ≤ (m - (i : ℕ)) * (b' * a) := by
      rw [Nat.mul_comm (m - (i : ℕ)) (b * a'), Nat.mul_comm (m - (i : ℕ)) (b' * a)]
      exact h5
    exact Nat.le_of_mul_le_mul_left h6 hmi
  have heq : e₁ * h₂ = e₂ * h₁ := le_antisymm (key hF₁ hF₂) (key hF₂ hF₁)
  have hcop₁ : Nat.Coprime h₁ e₁ := hF₁.2.2.1
  have hcop₂ : Nat.Coprime h₂ e₂ := hF₂.2.2.1
  have hh₁ : 1 ≤ h₁ := hF₁.1
  have hdvd₁ : h₁ ∣ h₂ := by
    have hd : h₁ ∣ e₁ * h₂ := ⟨e₂, by rw [heq, Nat.mul_comm]⟩
    exact hcop₁.dvd_of_dvd_mul_left hd
  have hdvd₂ : h₂ ∣ h₁ := by
    have hd : h₂ ∣ e₂ * h₁ := ⟨e₁, by rw [← heq, Nat.mul_comm]⟩
    exact hcop₂.dvd_of_dvd_mul_left hd
  have hh : h₁ = h₂ := Nat.dvd_antisymm hdvd₁ hdvd₂
  subst hh
  refine ⟨rfl, ?_⟩
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < h₁) heq

/-- **The class residual polynomial** at slope data `(u, ℓ)`: the side residual of a
chosen lift (junk `0` off the side's domain).  Lift-independent below the frame floor
by WFR §3 (`classResidualPoly_eq`). -/
noncomputable def classResidualPoly (π : O) {m K : ℕ} (c : Coeff O m K) (u ℓ : ℕ) :
    Polynomial (resField (X : Polynomial O)) :=
  if hne : (sideSet X (monicPoly (Classical.choose (proj_surjective O m K c))) u ℓ).Nonempty then
    if hH : ∃ H₀ : ℕ, npHgt X (monicPoly (Classical.choose (proj_surjective O m K c)))
        (sideMin X (monicPoly (Classical.choose (proj_surjective O m K c))) u ℓ hne)
          = (H₀ : ℕ∞) then
      resPoly π X (monicPoly (Classical.choose (proj_surjective O m K c))) u ℓ hne
        (Classical.choose hH)
    else 0
  else 0

variable [IsAdicComplete (maximalIdeal O) O]

/-- ★ **The transport** (WFR §3 consumed): below the frame floor the class residual is
EVERY lift's side residual. -/
theorem classResidualPoly_eq {π : O} (hπ : Irreducible π) {m K u ℓ : ℕ} (hl : 0 < ℓ)
    {c : Coeff O m K} (hvis : NPVisibleAt c u ℓ)
    {a : Fin m → O} (ha : proj O m K a = c)
    (hne : (sideSet X (monicPoly a) u ℓ).Nonempty) {H₀ : ℕ}
    (hH : npHgt X (monicPoly a) (sideMin X (monicPoly a) u ℓ hne) = (H₀ : ℕ∞)) :
    classResidualPoly π c u ℓ = resPoly π X (monicPoly a) u ℓ hne H₀ := by
  have ha₀ : proj O m K (Classical.choose (proj_surjective O m K c)) = c :=
    Classical.choose_spec (proj_surjective O m K c)
  -- the chosen lift's side set is nonempty (both side sets are the class side set)
  have hset := sideSet_monicPoly_eq hπ hl hvis ha
  have hset₀ := sideSet_monicPoly_eq hπ hl hvis ha₀
  have hne₀ : (sideSet X (monicPoly (Classical.choose (proj_surjective O m K c)))
      u ℓ).Nonempty := by
    rw [hset₀, ← hset]
    exact hne
  -- the chosen lift's support value is finite (the monic point caps it)
  have htop₀ : suppVal X (monicPoly (Classical.choose (proj_surjective O m K c))) u ℓ
      ≠ ⊤ := by
    have hle : suppVal X (monicPoly (Classical.choose (proj_surjective O m K c))) u ℓ
        ≤ ℓ • npHgt X (monicPoly (Classical.choose (proj_surjective O m K c))) m
          + ((u * m : ℕ) : ℕ∞) := by
      rw [suppVal, monicPoly_natDegree]
      exact Finset.inf_le (Finset.mem_range.mpr (by omega))
    rw [npHgt_monicPoly_top, smul_zero, zero_add] at hle
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle
  -- the chosen lift's side-min height is finite; name it
  have hntop₀ : npHgt X (monicPoly (Classical.choose (proj_surjective O m K c)))
      (sideMin X (monicPoly (Classical.choose (proj_surjective O m K c))) u ℓ hne₀)
        ≠ ⊤ :=
    npHgt_ne_top_of_onSide hl htop₀ (onSide_of_mem_sideSet (Finset.min'_mem _ hne₀))
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hntop₀
  have hw' : ((w : ℕ) : ℕ∞)
      = npHgt X (monicPoly (Classical.choose (proj_surjective O m K c)))
          (sideMin X (monicPoly (Classical.choose (proj_surjective O m K c))) u ℓ hne₀) :=
    hw
  have hex : ∃ H₀' : ℕ, npHgt X (monicPoly (Classical.choose (proj_surjective O m K c)))
      (sideMin X (monicPoly (Classical.choose (proj_surjective O m K c))) u ℓ hne₀)
        = (H₀' : ℕ∞) := ⟨w, hw'.symm⟩
  unfold classResidualPoly
  rw [dif_pos hne₀, dif_pos hex]
  exact (resPoly_monicPoly_eq hπ hl hvis ha₀ ha hne₀ hne
    (Classical.choose_spec hex) hH).2

/-- **The residual honesty lemma**: on the minimal face, the class residual is
NONCONSTANT with nonzero constant term (`natDegree ≥ 1`) — so the three sector
patterns carry their intended meaning, and §2c's dichotomy fires on every
split-sector class.  (Mechanism: `sideMax = m`, `sideMin < m`, and coprimality forces
`e' ∣ sideMax − sideMin`, so `sideDeg ≥ 1`; B.30 pins `natDegree = sideDeg`.) -/
theorem classResidualPoly_natDegree_pos {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    {c : Coeff O m K} (hF : MinFaceAt c h e') :
    0 < (classResidualPoly π c h e').natDegree
      ∧ (classResidualPoly π c h e').coeff 0 ≠ 0 := by
  obtain ⟨hh1, hhe, hcop, hface, hAm, hvis⟩ := hF
  have he' : 0 < e' := by omega
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  obtain ⟨i, j, hij, hAi, hAj⟩ := hface
  have hilt : i < m := lt_of_lt_of_le hij hAj.1
  obtain ⟨hOni, hsupp⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hAi ha
  obtain ⟨hOnm, -⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hAm ha
  have htop : suppVal X (monicPoly a) h e' ≠ ⊤ := by
    rw [hsupp]
    exact ENat.coe_ne_top _
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  have himem : i ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOni⟩
  have hmmem : m ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOnm⟩
  have hne : (sideSet X (monicPoly a) h e').Nonempty := ⟨i, himem⟩
  have hntop : npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) ≠ ⊤ :=
    npHgt_ne_top_of_onSide he' htop (onSide_of_mem_sideSet (Finset.min'_mem _ hne))
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hntop
  have hw' : ((w : ℕ) : ℕ∞)
      = npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) := hw
  have hcrp := classResidualPoly_eq hπ he' hvis ha hne hw'.symm
  have hnd := natDegree_resPoly hπ isKey_X he' hcop htop hne hw'.symm
  rw [hcrp]
  refine ⟨?_, hnd.2⟩
  rw [hnd.1]
  -- `sideMax = m` and `sideMin ≤ i < m`
  have hmax : sideMax X (monicPoly a) h e' hne = m := by
    unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ m hmmem)
    have h2 := Finset.max'_mem (sideSet X (monicPoly a) h e') hne
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    omega
  have hminle : sideMin X (monicPoly a) h e' hne ≤ i := by
    unfold sideMin
    exact Finset.min'_le _ i himem
  -- the two on-side equations, extracted to ℕ
  have hsupp_m : suppVal X (monicPoly a) h e' = ((h * m : ℕ) : ℕ∞) := by
    have h6 : e' • npHgt X (monicPoly a) m + ((h * m : ℕ) : ℕ∞)
        = suppVal X (monicPoly a) h e' := hOnm
    rw [npHgt_monicPoly_top, smul_zero, zero_add] at h6
    exact h6.symm
  have hOnmin : OnSide X (monicPoly a) h e' (sideMin X (monicPoly a) h e' hne) :=
    onSide_of_mem_sideSet (Finset.min'_mem _ hne)
  have h7 : e' • npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne)
      + ((h * sideMin X (monicPoly a) h e' hne : ℕ) : ℕ∞) = ((h * m : ℕ) : ℕ∞) := by
    rw [← hsupp_m]
    exact hOnmin
  rw [← hw'] at h7
  have h8 : e' * w + h * sideMin X (monicPoly a) h e' hne = h * m := by
    have h9 : ((e' * w + h * sideMin X (monicPoly a) h e' hne : ℕ) : ℕ∞)
        = ((h * m : ℕ) : ℕ∞) := by
      rw [← h7, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add]
    exact Nat.cast_inj.mp h9
  -- coprimality forces `e' ∣ m − sideMin`
  have hdvd : e' ∣ h * (m - sideMin X (monicPoly a) h e' hne) := by
    refine ⟨w, ?_⟩
    have hsplit : h * (m - sideMin X (monicPoly a) h e' hne)
        + h * sideMin X (monicPoly a) h e' hne = h * m := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (by omega : sideMin X (monicPoly a) h e' hne ≤ m)]
    have h10 := hsplit.trans h8.symm
    exact Nat.add_right_cancel h10
  obtain ⟨t, ht⟩ : e' ∣ (m - sideMin X (monicPoly a) h e' hne) :=
    hcop.symm.dvd_of_dvd_mul_left hdvd
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h10
    · rw [Nat.mul_zero] at ht
      omega
    · exact h10
  unfold sideDeg
  rw [hmax, ht, Nat.mul_div_cancel_left t he']
  exact htpos

end MinFace

/-! ## §2c — the split dichotomy over a field -/

section Dichotomy

/-- **The split dichotomy** (the split sector's semantic content, XHS-ready): over any
field, a nonconstant polynomial that is neither irreducible nor a proper prime power
factors as a product of two COPRIME monic nonconstant polynomials, up to a unit. -/
theorem exists_coprime_split_of_not_primary {F : Type*} [Field F] {R : Polynomial F}
    (hR0 : 0 < R.natDegree) (hni : ¬ Irreducible R)
    (hnp : ¬ ∃ (ψ : Polynomial F) (k : ℕ), Irreducible ψ ∧ 2 ≤ k ∧ Associated R (ψ ^ k)) :
    ∃ G H : Polynomial F, G.Monic ∧ H.Monic ∧ 0 < G.natDegree ∧ 0 < H.natDegree ∧
      IsCoprime G H ∧ Associated R (G * H) := by
  classical
  have hRne : R ≠ 0 := by
    intro h
    rw [h] at hR0
    simp at hR0
  have hR'm : (normalize R).Monic := Polynomial.monic_normalize hRne
  have hassoc : Associated R (normalize R) := associated_normalize R
  have hR'ne : normalize R ≠ 0 := fun h => hRne (normalize_eq_zero.mp h)
  have hR'irr : ¬ Irreducible (normalize R) := fun h => hni (hassoc.symm.irreducible h)
  have hR'unit : ¬ IsUnit (normalize R) := by
    intro h
    have h1 : normalize R = 1 := hR'm.eq_one_of_isUnit h
    rw [h1] at hassoc
    have h2 : IsUnit R := associated_one_iff_isUnit.mp hassoc
    have h3 := Polynomial.natDegree_eq_zero_of_isUnit h2
    omega
  obtain ⟨p, hp⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors hR'ne hR'unit
  have hpirr : Irreducible p :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
  have hpm : p.Monic := Uniformity.Density.IFCG17.monic_of_mem_normalizedFactors hp
  obtain ⟨g', hg'm, hgeq, hpg'⟩ :=
    Uniformity.Density.IFCG17.exists_primary_decomposition hR'm hp
  have hn1 : 1 ≤ (UniqueFactorizationMonoid.normalizedFactors (normalize R)).count p :=
    Multiset.count_pos.mpr hp
  have hpdeg : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
    · exfalso
      have h1 : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
      have h2 : p.coeff 0 ≠ 0 := by
        intro h3
        rw [h3, map_zero] at h1
        exact hpirr.ne_zero h1
      have h4 : IsUnit p := by
        rw [h1]
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr h2)
      exact hpirr.not_isUnit h4
    · exact h0
  by_cases hunit : IsUnit g'
  · -- the cofactor is trivial: `normalize R` IS a prime power — excluded by the hypotheses
    exfalso
    have h1 : g' = 1 := hg'm.eq_one_of_isUnit hunit
    rw [h1, mul_one] at hgeq
    rcases Nat.lt_or_ge ((UniqueFactorizationMonoid.normalizedFactors
        (normalize R)).count p) 2 with h2 | h2
    · have hn1' : (UniqueFactorizationMonoid.normalizedFactors
          (normalize R)).count p = 1 := by omega
      rw [hn1', pow_one] at hgeq
      exact hR'irr (hgeq ▸ hpirr)
    · refine hnp ⟨p, (UniqueFactorizationMonoid.normalizedFactors
        (normalize R)).count p, hpirr, h2, ?_⟩
      rw [← hgeq]
      exact hassoc
  · -- the genuine split: `G = p^n`, `H = g'`, coprime by `p ∤ g'`
    have hg'deg : 0 < g'.natDegree := by
      rcases Nat.eq_zero_or_pos g'.natDegree with h0 | h0
      · exact absurd ((Polynomial.eq_one_of_monic_natDegree_zero hg'm h0) ▸ isUnit_one)
          hunit
      · exact h0
    have hcop : IsCoprime
        (p ^ ((UniqueFactorizationMonoid.normalizedFactors (normalize R)).count p)) g' :=
      (hpirr.coprime_iff_not_dvd.mpr hpg').pow_left
    refine ⟨p ^ ((UniqueFactorizationMonoid.normalizedFactors (normalize R)).count p),
      g', hpm.pow _, hg'm, ?_, hg'deg, hcop, ?_⟩
    · rw [Polynomial.natDegree_pow]
      exact Nat.mul_pos hn1 hpdeg
    · rw [← hgeq]
      exact hassoc

end Dichotomy

/-! ## §3 — ★★ the trichotomy partition of the remainder carrier -/

section Sectors

/-- The remainder carrier (the set whose cardinality is `coneRemainderCount`): the
`σ`-decided shallow stratum classes outside every admissible pure-face box. -/
def remainderCarrier (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (Coeff O m (M + m)) :=
  (decidedSet O m σ (M + m)
      ∩ levelZeroStratum O m (M + m) (X ^ m)
      ∩ shallowSet O m (M + m))
    \ pureFaceSet O m (M + m)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

theorem coneRemainderCount_eq_card (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    coneRemainderCount O m σ M = Nat.card (remainderCarrier O m σ M) := rfl

/-- **The LEAF sector**: minimal-face residual IRREDUCIBLE — the recursion's leaves
(decided by `ResidualLeafLaw` at the face parameters). -/
def leafSector (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (Coeff O m (M + m)) :=
  {c | c ∈ remainderCarrier O m σ M ∧ ∃ h e' : ℕ, MinFaceAt c h e'
    ∧ Irreducible (classResidualPoly π c h e')}

/-- **The POWER sector**: minimal-face residual a PROPER power of one irreducible —
the fractional-recentring step's territory (the tower recursion). -/
def powerSector (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (Coeff O m (M + m)) :=
  {c | c ∈ remainderCarrier O m σ M ∧ ∃ h e' : ℕ, MinFaceAt c h e'
    ∧ ¬ Irreducible (classResidualPoly π c h e')
    ∧ ∃ (ψ : Polynomial (resField (X : Polynomial O))) (k : ℕ),
        Irreducible ψ ∧ 2 ≤ k ∧ Associated (classResidualPoly π c h e') (ψ ^ k)}

/-- **The SPLIT sector**: minimal-face residual neither irreducible nor a proper prime
power — coprime-reducible (§2c), the smaller-mass convolution's territory (XHS §4
refines every lift). -/
def splitSector (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) :
    Set (Coeff O m (M + m)) :=
  {c | c ∈ remainderCarrier O m σ M ∧ ∃ h e' : ℕ, MinFaceAt c h e'
    ∧ ¬ Irreducible (classResidualPoly π c h e')
    ∧ ¬ ∃ (ψ : Polynomial (resField (X : Polynomial O))) (k : ℕ),
        Irreducible ψ ∧ 2 ≤ k ∧ Associated (classResidualPoly π c h e') (ψ ^ k)}

def leafSectorCount (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  Nat.card (leafSector O π m σ M)

def powerSectorCount (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  Nat.card (powerSector O π m σ M)

def splitSectorCount (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (π : O) (m : ℕ) (σ : FactorizationType) (M : ℕ) : ℕ :=
  Nat.card (splitSector O π m σ M)

/-- ★★ **THE TRICHOTOMY PARTITION** (set form): the remainder carrier IS the disjoint
union of the three recursion sectors — every carrier class has a (unique) minimal
face, and its class residual is irreducible, a proper prime power, or coprime-split. -/
theorem remainderCarrier_eq_sectors {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (π : O) (M : ℕ) :
    remainderCarrier O m σ M
      = splitSector O π m σ M ∪ powerSector O π m σ M ∪ leafSector O π m σ M := by
  ext c
  constructor
  · intro hc
    have hc' : c ∈ remainderCarrier O m σ M := hc
    obtain ⟨⟨⟨-, hstr⟩, hsh⟩, -⟩ := hc
    have hstr' : ∀ i : Fin m, 1 ≤ resOrd (c i) :=
      (mem_stratum_X_pow_iff (by omega : 1 ≤ M + m) c).1 hstr
    obtain ⟨h, e', hF⟩ := exists_minFaceAt_of_shallow (by omega : m ≤ M + m) hstr' hsh
    by_cases hirr : Irreducible (classResidualPoly π c h e')
    · exact Or.inr ⟨hc', h, e', hF, hirr⟩
    · by_cases hpow : ∃ (ψ : Polynomial (resField (X : Polynomial O))) (k : ℕ),
          Irreducible ψ ∧ 2 ≤ k ∧ Associated (classResidualPoly π c h e') (ψ ^ k)
      · exact Or.inl (Or.inr ⟨hc', h, e', hF, hirr, hpow⟩)
      · exact Or.inl (Or.inl ⟨hc', h, e', hF, hirr, hpow⟩)
  · rintro ((⟨hc, -⟩ | ⟨hc, -⟩) | ⟨hc, -⟩) <;> exact hc

theorem sectors_disjoint {m : ℕ} (σ : FactorizationType) (π : O) (M : ℕ) :
    Disjoint (splitSector O π m σ M) (powerSector O π m σ M)
      ∧ Disjoint (splitSector O π m σ M ∪ powerSector O π m σ M)
          (leafSector O π m σ M) := by
  constructor
  · rw [Set.disjoint_left]
    rintro c ⟨-, h₁, e₁, hF₁, -, hnp₁⟩ ⟨-, h₂, e₂, hF₂, -, hpow₂⟩
    obtain ⟨hh, he⟩ := minFaceAt_unique hF₁ hF₂
    subst hh
    subst he
    exact hnp₁ hpow₂
  · rw [Set.disjoint_left]
    rintro c hc ⟨-, h₂, e₂, hF₂, hirr₂⟩
    rcases hc with ⟨-, h₁, e₁, hF₁, hni₁, -⟩ | ⟨-, h₁, e₁, hF₁, hni₁, -⟩ <;>
    · obtain ⟨hh, he⟩ := minFaceAt_unique hF₁ hF₂
      subst hh
      subst he
      exact hni₁ hirr₂

/-- ★★ **THE TRICHOTOMY PARTITION** (count form): exact at every finite level, every
mass, every type, every complete DVR, every uniformizer. -/
theorem coneRemainderCount_eq_sector_sum {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (π : O) (M : ℕ) :
    coneRemainderCount O m σ M
      = splitSectorCount O π m σ M + powerSectorCount O π m σ M
        + leafSectorCount O π m σ M := by
  classical
  haveI : Fintype (Coeff O m (M + m)) := Fintype.ofFinite _
  obtain ⟨hd₁, hd₂⟩ := sectors_disjoint σ π M
  rw [coneRemainderCount_eq_card, remainderCarrier_eq_sectors hm σ π M]
  unfold splitSectorCount powerSectorCount leafSectorCount
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Set.ncard_union_eq hd₂ (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq hd₁ (Set.toFinite _) (Set.toFinite _)]

end Sectors

/-! ## §4 — ★★ the sector laws and the assembly -/

section SectorLaws

/-- **The SPLIT sector law at `(m, σ)`** — the convolution step's residue: a uniform
rational limit for the normalized split-sector count.  (Discharge territory: XHS §4's
coprime refinement to strictly smaller masses + IFCG17's convolution counting.) -/
def SplitSectorLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (splitSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- **The POWER sector law at `(m, σ)`** — the fractional-recentring step's residue.
(Discharge territory: the recentred copy at the face — IFCG20's machinery at
fractional centres, C136's tower — with strictly smaller residual mass.) -/
def PowerSectorLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (powerSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- **The LEAF sector law at `(m, σ)`** — the leaf census' residue.  (Its decision
content is §1's `ResidualLeafLaw`; the census combines the decided blocks with the
sub-face remainder.) -/
def LeafSectorLaw (m : ℕ) (σ : FactorizationType) : Prop :=
  ZcURLim (fun O _ _ _ _ _ π M =>
    (leafSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m)))

/-- ★★ **THE ASSEMBLY**: the three sector laws at `(m, σ)` fire the remainder law at
`(m, σ)` — the trichotomy partition is exact at every level, so the law's value is the
sum of the three sector values. -/
theorem coneRemainderLaw_of_sectorLaws {m : ℕ} (hm : 0 < m) (σ : FactorizationType)
    (hS : SplitSectorLaw m σ) (hP : PowerSectorLaw m σ) (hL : LeafSectorLaw m σ) :
    ConeRemainderLaw m σ := by
  refine ((hS.add hP).add hL).congr ?_
  intro O _ _ _ _ _ π hπ M
  show (splitSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      + (powerSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
      + (leafSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    = (coneRemainderCount O m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
  rw [coneRemainderCount_eq_sector_sum hm σ π M]
  push_cast
  ring

/-- ★ **Nonvacuity of the sector-law families — the unramified instances fire**: at
every mass and every unramified type all three sectors are EMPTY (UZL's forcing keeps
every unramified decision off the shallow stratum), so all three laws hold, with value
`0`. -/
theorem sectorLaws_unramified {m : ℕ} (σ : FactorizationType)
    (hunr : ∀ p ∈ σ.data, p.1 = 1) :
    SplitSectorLaw m σ ∧ PowerSectorLaw m σ ∧ LeafSectorLaw m σ := by
  have hcar : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (M : ℕ),
      remainderCarrier O m σ M = (∅ : Set (Coeff O m (M + m))) := by
    intro O _ _ _ _ _ M
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨⟨hdec, hstr⟩, hsh⟩, -⟩
    exact Uniformity.Density.IFCG33.not_decidedAt_unramified_of_shallow
      (by omega : m ≤ M + m) hstr hsh hunr hdec
  refine ⟨ZcURLim_zero.congr ?_, ZcURLim_zero.congr ?_, ZcURLim_zero.congr ?_⟩
  · intro O _ _ _ _ _ π hπ M
    show (0 : ℝ)
      = (splitSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    have hsub : splitSector O π m σ M ⊆ remainderCarrier O m σ M := fun c hc => hc.1
    have h1 : splitSectorCount O π m σ M = 0 := by
      unfold splitSectorCount
      rw [Set.subset_eq_empty hsub (hcar O M), Nat.card_coe_set_eq, Set.ncard_empty]
    rw [h1]
    simp
  · intro O _ _ _ _ _ π hπ M
    show (0 : ℝ)
      = (powerSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    have hsub : powerSector O π m σ M ⊆ remainderCarrier O m σ M := fun c hc => hc.1
    have h1 : powerSectorCount O π m σ M = 0 := by
      unfold powerSectorCount
      rw [Set.subset_eq_empty hsub (hcar O M), Nat.card_coe_set_eq, Set.ncard_empty]
    rw [h1]
    simp
  · intro O _ _ _ _ _ π hπ M
    show (0 : ℝ)
      = (leafSectorCount O π m σ M : ℝ) / ((residueCard O : ℕ) : ℝ) ^ (m * (M + m))
    have hsub : leafSector O π m σ M ⊆ remainderCarrier O m σ M := fun c hc => hc.1
    have h1 : leafSectorCount O π m σ M = 0 := by
      unfold leafSectorCount
      rw [Set.subset_eq_empty hsub (hcar O M), Nat.card_coe_set_eq, Set.ncard_empty]
    rw [h1]
    simp

end SectorLaws

/-! ## §5 — ★ the spanning leaf decisions (the fired instances) -/

section Spanning

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- The lift-side data of a spanning face: nonempty side set with `sideMin = 0`,
`sideMax = m`, finite support. -/
private theorem spanning_side_data {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    (hm0 : 0 < m) (he' : 0 < e')
    {c : Coeff O m K} (h0 : NPAttains c h e' 0) (hmm : NPAttains c h e' m)
    (hvis : NPVisibleAt c h e') {a : Fin m → O} (ha : proj O m K a = c) :
    ∃ hne : (sideSet X (monicPoly a) h e').Nonempty,
      sideMin X (monicPoly a) h e' hne = 0 ∧ sideMax X (monicPoly a) h e' hne = m
        ∧ suppVal X (monicPoly a) h e' ≠ ⊤ := by
  obtain ⟨hOn0, hsupp⟩ := onSide_monicPoly_of_npAttains hπ he' hvis h0 ha
  obtain ⟨hOnm, -⟩ := onSide_monicPoly_of_npAttains hπ he' hvis hmm ha
  have htop : suppVal X (monicPoly a) h e' ≠ ⊤ := by
    rw [hsupp]
    exact ENat.coe_ne_top _
  have hdegm : (monicPoly a).natDegree = m := monicPoly_natDegree a
  have h0mem : (0 : ℕ) ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOn0⟩
  have hmmem : m ∈ sideSet X (monicPoly a) h e' :=
    mem_sideSet_iff'.mpr ⟨by omega, hOnm⟩
  refine ⟨⟨0, h0mem⟩, ?_, ?_, htop⟩
  · unfold sideMin
    exact Nat.le_zero.mp (Finset.min'_le _ 0 h0mem)
  · unfold sideMax
    refine le_antisymm ?_ (Finset.le_max' _ m hmmem)
    have h2 := Finset.max'_mem (sideSet X (monicPoly a) h e') ⟨0, h0mem⟩
    obtain ⟨h3, -⟩ := mem_sideSet_iff'.mp h2
    omega

/-- ★ **The spanning leaf decision**: a stratum class whose face `h/e'` spans `[0, m]`
(`m = e'·d`, coprime, visible) with IRREDUCIBLE class residual is DECIDED
`⟨{(e', d)}⟩` — conditional exactly on the leaf law at `(e', d)`. -/
theorem decidedAt_of_spanning_leaf {e' d : ℕ} (hL : ResidualLeafLaw e' d)
    {π : O} (hπ : Irreducible π) {m K h : ℕ} (hm0 : 0 < m) (hh : 0 < h)
    (he' : 0 < e') (hcop : Nat.Coprime h e') (hd : m = e' * d)
    {c : Coeff O m K} (hstr : c ∈ levelZeroStratum O m K (X ^ m))
    (h0 : NPAttains c h e' 0) (hmm : NPAttains c h e' m) (hvis : NPVisibleAt c h e')
    (hirr : Irreducible (classResidualPoly π c h e')) :
    DecidedAt O m ⟨{(e', d)}⟩ K c := by
  intro a ha
  have hpure : IsPure X (monicPoly a) h e' :=
    isPure_monicPoly_of_face hπ hm0 he' h0 hmm hvis ha
  have hres : (monicPoly a).map (IsLocalRing.residue O) = X ^ (e' * d) := by
    have h1 : (monicPoly a).map (IsLocalRing.residue O) = X ^ (monicPoly a).natDegree := by
      rw [monicPoly_natDegree]
      exact hstr a ha
    rw [h1, monicPoly_natDegree, hd]
  obtain ⟨hne, hmin, hmax, htop⟩ := spanning_side_data hπ hm0 he' h0 hmm hvis ha
  have hsd : sideDeg X (monicPoly a) h e' hne = d := by
    unfold sideDeg
    rw [hmin, hmax, Nat.sub_zero, hd]
    exact Nat.mul_div_cancel_left d he'
  have hntop : npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) ≠ ⊤ :=
    npHgt_ne_top_of_onSide he' htop (onSide_of_mem_sideSet (Finset.min'_mem _ hne))
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hntop
  have hw' : ((w : ℕ) : ℕ∞)
      = npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne) := hw
  have hcrp := classResidualPoly_eq hπ he' hvis ha hne hw'.symm
  rw [hcrp] at hirr
  exact hL O π hπ h hh hcop (monicPoly a) (monicPoly_monic a) hpure hne hsd hres
    w hw'.symm hirr

/-- ★ **CN2 recovered through the leaf engine** (`d = 1`, `e' = m`): the Eisenstein
face decision is the spanning instance of the UNCONDITIONAL `d = 1` leaf law — the
degree-1 class residual is automatically irreducible. -/
theorem decidedAt_of_spanning_eisenstein {π : O} (hπ : Irreducible π) {m K h : ℕ}
    (hm0 : 0 < m) (hh : 0 < h) (hcop : Nat.Coprime h m)
    {c : Coeff O m K} (hstr : c ∈ levelZeroStratum O m K (X ^ m))
    (h0 : NPAttains c h m 0) (hmm : NPAttains c h m m) (hvis : NPVisibleAt c h m) :
    DecidedAt O m ⟨{(m, 1)}⟩ K c := by
  -- the degree-1 class residual is automatically irreducible
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  obtain ⟨hne, hmin, hmax, htop⟩ := spanning_side_data hπ hm0 hm0 h0 hmm hvis ha
  have hntop : npHgt X (monicPoly a) (sideMin X (monicPoly a) h m hne) ≠ ⊤ :=
    npHgt_ne_top_of_onSide hm0 htop (onSide_of_mem_sideSet (Finset.min'_mem _ hne))
  obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp hntop
  have hw' : ((w : ℕ) : ℕ∞)
      = npHgt X (monicPoly a) (sideMin X (monicPoly a) h m hne) := hw
  have hcrp := classResidualPoly_eq hπ hm0 hvis ha hne hw'.symm
  have hsd1 : sideDeg X (monicPoly a) h m hne = 1 := by
    unfold sideDeg
    rw [hmin, hmax, Nat.sub_zero]
    exact Nat.div_self hm0
  have hnd := natDegree_resPoly hπ isKey_X hm0 hcop htop hne hw'.symm
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hRne : resPoly π X (monicPoly a) h m hne w ≠ 0 := by
    intro h1
    have h2 := hnd.2
    rw [h1] at h2
    simp at h2
  have hdeg1 : (resPoly π X (monicPoly a) h m hne w).natDegree = 1 := by
    rw [hnd.1, hsd1]
  have hirr : Irreducible (resPoly π X (monicPoly a) h m hne w) :=
    Polynomial.irreducible_of_degree_eq_one
      ((Polynomial.degree_eq_iff_natDegree_eq hRne).mpr hdeg1)
  rw [← hcrp] at hirr
  exact decidedAt_of_spanning_leaf (residualLeafLaw_one hm0) hπ hm0 hh hm0 hcop
    (Nat.mul_one m).symm hstr h0 hmm hvis hirr

end Spanning

/-! ## §6 — ★★★ the census front through the trichotomy -/

section Front

open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)

/-- The ramified `e ≥ 5` remainder laws from the three sector laws (the front's `hR`
feeder, in the recursion's own descent shape: each mass consumes the `< e` decided
value laws). -/
theorem coneRemainderLaw_ram5_of_sectorLaws
    (hSplit : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitSectorLaw e σ)
    (hPow : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerSectorLaw e σ)
    (hLeaf : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → LeafSectorLaw e σ) :
    ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ConeRemainderLaw e σ :=
  fun e he hsm σ hσ hwit hram =>
    coneRemainderLaw_of_sectorLaws (by omega) σ
      (hSplit e he hsm σ hσ hwit hram) (hPow e he hsm σ hσ hwit hram)
      (hLeaf e he hsm σ hσ hwit hram)

/-- ★★★ **THE CENSUS FRONT THROUGH THE TRICHOTOMY**: the all-degree decided slice
rests on EXACTLY the three sector laws at `(e ≥ 5, σ ramified)` — each with the
smaller-mass decided value laws as premises — plus the five `e = 4` even-ramification
remainder laws.  The unramified types are closed by UZL at every mass; the bridge
family is closed by IFCG32. -/
theorem decidedSliceAt_all_of_sectorLaws
    (hSplit : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → SplitSectorLaw e σ)
    (hPow : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerSectorLaw e σ)
    (hLeaf : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → LeafSectorLaw e σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG33.decidedSliceAt_all_of_ram5_even4_bridge
    (coneRemainderLaw_ram5_of_sectorLaws hSplit hPow hLeaf) hR4
    (fun _ e h2δ _ => Uniformity.Density.IFCG32.unramifiedBlockBridge_all
      (by omega : 1 ≤ _) e)

end Front

end Uniformity.Density.IFCG35

end

/-! ## AXCHECK FOOTER — §§2–3 partition arithmetic expects Lean core
`{propext, Classical.choice, Quot.sound}`; everything touching the landed transports
and the front expects Lean core PLUS exactly the signed gate-(b) cite
`Uniformity.Density.Leaf.exists_slope_factorization` (B.42).  The C.33 cites must NOT
occur. -/

#print axioms Uniformity.Density.IFCG35.residualLeafLaw_one
#print axioms Uniformity.Density.IFCG35.residualLeafLaw_of_supply
#print axioms Uniformity.Density.IFCG35.exists_minFaceAt_of_shallow
#print axioms Uniformity.Density.IFCG35.minFaceAt_unique
#print axioms Uniformity.Density.IFCG35.classResidualPoly_eq
#print axioms Uniformity.Density.IFCG35.classResidualPoly_natDegree_pos
#print axioms Uniformity.Density.IFCG35.exists_coprime_split_of_not_primary
#print axioms Uniformity.Density.IFCG35.remainderCarrier_eq_sectors
#print axioms Uniformity.Density.IFCG35.coneRemainderCount_eq_sector_sum
#print axioms Uniformity.Density.IFCG35.coneRemainderLaw_of_sectorLaws
#print axioms Uniformity.Density.IFCG35.sectorLaws_unramified
#print axioms Uniformity.Density.IFCG35.decidedAt_of_spanning_leaf
#print axioms Uniformity.Density.IFCG35.decidedAt_of_spanning_eisenstein
#print axioms Uniformity.Density.IFCG35.decidedSliceAt_all_of_sectorLaws
