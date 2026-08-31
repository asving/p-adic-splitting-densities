/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import Uniformity.ChapI.IFCG57
import Uniformity.ChapI.IFCG58

/-!
# Uniformity.ChapI.IFCG59 — [TBT 2026-08-31] the two-block factorization transport
at the leaf sub-face sector, and the singleton-σ leaf fire

Stage TBT of the cone census (design record `runs/wave-c/verdict_TBT.md`; consumes
LSC = `IFCG57`, PCD = `IFCG58`, and — through them — XHS/SDL/RIS/IFCG26's engines).
LSC's discharge pointer: the sub-face leaf cell factors, at the lift level, as an
`(h, e')`-pure block times a rest of complementary degree, and "type additivity along
the two-block split forces `|σ.data| ≥ 2` off the spanning locus — landing just THAT
would fire `LeafSectorLaw m ⟨{(e', d)}⟩` outright for all singleton types."  This file
lands exactly that transport, PINNED:

* **§0 THE BRIDGE** (Lean-core): a lift on-side at abscissa `0` forces the CLASS
  attainment at `0` (`npAttains_zero_of_onSide`) — the converse transport of
  IFCG26 §1, at the one abscissa the sub-face carrier excludes.
* **§1 THE UN-PINNED TRANSPORT** (`subface_two_block_split`): EVERY lift of a
  sub-face leaf cell splits as `monicPoly a = g · R` with `g` monic `(h, e')`-pure,
  `R` monic, BOTH of positive degree, and the class type decomposes additively:
  `σ.data = (typeOf g).data + (typeOf R).data`.  Mechanism: IFCG26 §2's packaged
  B.42 engine (`exists_pure_factor_of_two_point_side`) + §0 (the rest is nontrivial
  precisely because the face does not reach `0`) + CN-03's `typeOf_mul`.
* **§2 THE SINGLETON FIRE**: `leafSubSector = ∅` whenever `Multiset.card σ.data ≤ 1`
  (`leafSubSector_eq_empty_of_card_le_one`), hence `LeafSubfaceLaw m σ` holds
  outright there, hence ★★★ `leafSectorLaw_singleton`: **`LeafSectorLaw m ⟨{p}⟩`
  UNCONDITIONALLY at every singleton type and every `0 < m`** — master row 5 is
  CLOSED at singleton σ.
* **§3 THE PINNED TRANSPORT** (`subface_two_block_transport`): the block's type is
  pinned — `typeOf g = ⟨{(e', d)}⟩` with `g.natDegree = e' * d`, `d` the face's
  residual degree, `e' * d < m`, and `σ.data = (e', d) ::ₘ (typeOf R).data`.
  Mechanism: B.39a §7's general product laws (sides/residuals of `g · R`
  concatenate/multiply) identify `resPoly g` with the class residual up to the unit
  `resPoly R` (irreducibility forces the rest's side residual to degree `0`), and
  IFCG37's unconditional `residualLeafLaw_all` reads the type off the block.
  Corollary `face_block_mem_type`: `(e', d) ∈ σ.data` — the visible sub-face's
  block type is an ENTRY of the class type.
* **§4 THE MASTERS RECOMPUTED**: both spines' row 5 premises weaken to
  `LeafSubfaceLaw` at NON-SINGLETON σ only (`2 ≤ Multiset.card σ.data` joins the
  guards): `decidedSliceAt_all_of_visCensus'` (PCD's newest spine) and
  `decidedSliceAt_all_of_MASTER''` / `capstoneHypotheses_of_MASTER''` (LSC's
  FC/Eis spine).

## Honest scope

NOT proved here: `LeafSubfaceLaw m σ` at non-singleton σ — the exact count of the
sub-face cells (the face digit box convolved with the mass-`(m − e'·d)` rest at the
complementary type).  §3 pins the correspondence's IMAGE data exactly; the COUNT
needs the depth-graded fiber law of the two-block class correspondence (the factor
classes are pinned only mod `π^{N − v(Res)}`, SDL's refutation genre; at disjoint
slopes `v(Res)` is polygon-determined — `v(Res(g,R)) = deg R · v₀(g)`-type mixed
term — RCD's tiling toolkit is the discharge territory).  Nothing weakened:
`LeafSubfaceLaw`/`LeafSectorLaw` statements are IFCG57/IFCG35's, byte-untouched.

## Axiom fence (machine-exact at landing)

§0 and the §2 law-level wrappers are pure Lean core
`{propext, Classical.choice, Quot.sound}` except where they consume the split:
§1/§2's sector theorems and §3 inherit Lean core + EXACTLY the owner-signed
gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization` (B.42, through
IFCG26 §2 / IFCG35 / IFCG37 — never re-consumed); the §4 spine wrappers inherit
their spines' footprints (+ `agnprw_termination` for the capstone, ID12's,
previously declared).  The C.33 cites and `AX_cellRecursion` must NOT occur.
Zero sorries at landing.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace Uniformity.Density.IFCG59

open IsLocalRing Polynomial
open Uniformity.Density.Induction
open Uniformity.Density.Leaf
open Uniformity.Density.IFCG22 (classCoeffVal npHeight classNPSupport NPAttains
  ClassNPFace NPVisibleAt classNPSupport_le_apply)
open Uniformity.Density.IFCG23 (le_npHgt_monicPoly npHgt_monicPoly_eq
  npHgt_monicPoly_top)
open Uniformity.Density.IFCG24 (ZcURLim ZcURLim_zero ConeRemainderLaw)
open Uniformity.Density.IFCG26 (onSide_monicPoly_of_npAttains
  exists_pure_factor_of_two_point_side mem_sideSet_of_onSide)
open Uniformity.Density.IFCG14 (DecidedValueLaw Witnessed)
open Uniformity.Density.IFCG35 (MinFaceAt minFaceAt_unique minFaceAt_support
  classResidualPoly classResidualPoly_eq leafSector LeafSectorLaw)
open Uniformity.Density.IFCG57 (leafSubSector leafSubCount LeafSubfaceLaw
  leafSectorLaw_of_subface)

attribute [local instance] Classical.propDecidable

/-! ## §0 — the kit: the abscissa-0 bridge and the side witnesses -/

section Kit

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)]

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

/-- The monic top point: the x-polygon height of a monic polynomial at its degree
abscissa is `0`. -/
private theorem npHgt_monic_top {g : Polynomial O} (hg : g.Monic) :
    npHgt X g g.natDegree = 0 := by
  rw [npHgt_X, hg.coeff_natDegree]
  exact IsDiscreteValuationRing.addVal_one

/-- The monic point caps the support value: `suppVal X g u ℓ ≠ ⊤` for monic `g`. -/
private theorem suppVal_ne_top_of_monic {g : Polynomial O} (hg : g.Monic) (u ℓ : ℕ) :
    suppVal X g u ℓ ≠ ⊤ := by
  have hle : suppVal X g u ℓ ≤ ℓ • npHgt X g g.natDegree + ((u * g.natDegree : ℕ) : ℕ∞) := by
    rw [suppVal]
    exact Finset.inf_le (Finset.mem_range.mpr (by omega))
  rw [npHgt_monic_top hg, smul_zero, zero_add] at hle
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle

/-- ★ **THE ABSCISSA-0 BRIDGE** (the converse transport at the excluded corner): if
some lift of `c` is ON-side at abscissa `0` for a VISIBLE slope datum whose lift
support value is the class support, then the CLASS polygon attains the face at `0`.
(The on-side equation pins the corner valuation strictly below the frame floor, so
the windowed read is exact and the class equation follows.) -/
theorem npAttains_zero_of_onSide {π : O} (hπ : Irreducible π) {m K h e' : ℕ}
    (hm0 : 0 < m) (he'0 : 0 < e') {c : Coeff O m K} (hvis : NPVisibleAt c h e')
    {a : Fin m → O} (ha : proj O m K a = c)
    (hO0 : OnSide X (monicPoly a) h e' 0)
    (hsupp : suppVal X (monicPoly a) h e' = (classNPSupport c h e' : ℕ∞)) :
    NPAttains c h e' 0 := by
  -- the on-side equation at 0, with the support identified
  have h1 : e' • npHgt X (monicPoly a) 0 + ((h * 0 : ℕ) : ℕ∞)
      = (classNPSupport c h e' : ℕ∞) := by
    rw [← hsupp]; exact hO0
  rw [Nat.mul_zero, Nat.cast_zero, add_zero] at h1
  -- the corner height is finite
  have hne : npHgt X (monicPoly a) 0 ≠ ⊤ := by
    intro htop
    rw [htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast he'0.ne' : (e' : ℕ∞) ≠ 0)] at h1
    exact (ENat.coe_ne_top _) h1.symm
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp hne
  have hv' : npHgt X (monicPoly a) 0 = ((v : ℕ) : ℕ∞) := hv.symm
  -- the ℕ-level corner equation `e' * v = classNPSupport`
  have h2 : e' * v = classNPSupport c h e' := by
    rw [hv', nsmul_eq_mul, ← Nat.cast_mul] at h1
    exact_mod_cast h1
  -- visibility puts the corner strictly below the frame floor
  have hvK : v < K := by
    have h3 : classNPSupport c h e' < e' * K := hvis
    have h4 : e' * v < e' * K := by omega
    exact Nat.lt_of_mul_lt_mul_left h4
  -- the windowed read is exact at the corner
  have hle : ((classCoeffVal c ⟨0, hm0⟩ : ℕ) : ℕ∞) ≤ npHgt X (monicPoly a) 0 :=
    le_npHgt_monicPoly hπ ha hm0
  have hccK : classCoeffVal c ⟨0, hm0⟩ < K := by
    rw [hv'] at hle
    have : classCoeffVal c ⟨0, hm0⟩ ≤ v := by exact_mod_cast hle
    omega
  have hcc : npHgt X (monicPoly a) 0 = ((classCoeffVal c ⟨0, hm0⟩ : ℕ) : ℕ∞) :=
    npHgt_monicPoly_eq hπ ha hm0 hccK
  have hveq : classCoeffVal c ⟨0, hm0⟩ = v := by
    rw [hv'] at hcc
    exact_mod_cast hcc.symm
  -- assemble the class attainment
  refine ⟨Nat.zero_le m, ?_⟩
  have hnp0 : npHeight c 0 = classCoeffVal c ⟨0, hm0⟩ := by
    unfold Uniformity.Density.IFCG22.npHeight
    rw [dif_pos hm0]
  rw [hnp0, hveq, Nat.mul_zero, Nat.add_zero]
  exact h2

/-- The type data of a positive-degree monic polynomial is nonempty. -/
private theorem typeOf_data_ne_zero {g : Polynomial O} (hg : g.Monic)
    (hd : 0 < g.natDegree) : (typeOf g).data ≠ 0 := by
  intro h0
  have hdeg := typeOf_degree hg
  rw [FactorizationType.degree, h0] at hdeg
  simp at hdeg
  omega

end Kit

/-! ## §1 — ★★ THE UN-PINNED TRANSPORT: every lift of a sub-face leaf cell splits,
and the class type decomposes additively across the split -/

section Split

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **THE GENERAL TWO-BLOCK SPLIT WITH TYPE ADDITIVITY** (the core, residual-genre
free): a σ-DECIDED stratum class at ANY level whose minimal face is NOT attained at
abscissa `0` has every lift factoring as a monic `(h, e')`-pure block `g` times a
monic rest `R`, BOTH of positive degree (the rest is nontrivial because the face does
not reach `0`), and the class type decomposes additively:
`σ.data = (typeOf g).data + (typeOf R).data`.  No hypothesis on the class residual —
this serves the leaf sub-face sector (§2/§3) AND the split/power cells' sub-face
strata (row 3's cell-side territory).  Consumes IFCG26 §2's packaged B.42 engine and
CN-03's `typeOf_mul`. -/
theorem two_block_split_of_not_attained_zero {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm0 : 0 < m) {σ : FactorizationType} {K : ℕ} {c : Coeff O m K}
    (hdec : Uniformity.Density.DecidedAt O m σ K c)
    (hstr : c ∈ levelZeroStratum O m K (X ^ m))
    {h e' : ℕ} (hF : MinFaceAt c h e') (hnA0 : ¬ NPAttains c h e' 0)
    {a : Fin m → O} (ha : proj O m K a = c) :
    ∃ g R : Polynomial O, g.Monic ∧ R.Monic ∧ monicPoly a = g * R
      ∧ 0 < g.natDegree ∧ 0 < R.natDegree ∧ IsPure X g h e'
      ∧ σ.data = (typeOf g).data + (typeOf R).data := by
  have hh1 : 1 ≤ h := hF.1
  have hhe : h < e' := hF.2.1
  have hcop : Nat.Coprime h e' := hF.2.2.1
  have hface : ClassNPFace c h e' := hF.2.2.2.1
  have hvis : NPVisibleAt c h e' := hF.2.2.2.2.2
  have he'0 : 0 < e' := by omega
  -- the two attained abscissae transport to lift-side points
  obtain ⟨i, j, hij, hAi, hAj⟩ := hface
  obtain ⟨hOi, hsupp⟩ := onSide_monicPoly_of_npAttains hπ he'0 hvis hAi ha
  obtain ⟨hOj, -⟩ := onSide_monicPoly_of_npAttains hπ he'0 hvis hAj ha
  have htop : suppVal X (monicPoly a) h e' ≠ ⊤ := by
    rw [hsupp]
    exact ENat.coe_ne_top _
  -- the stratum pins the residue
  have hres : (monicPoly a).map (residue O) = X ^ (monicPoly a).natDegree := by
    rw [monicPoly_natDegree]
    exact hstr a ha
  -- THE B.42 ENGINE (IFCG26 §2, packaged): the two-point side splits off a pure block
  obtain ⟨g, R, hgm, hRm, hgpure, hgd, heq⟩ :=
    exists_pure_factor_of_two_point_side hπ (monicPoly_monic a) hres (by omega) he'0
      hcop hij (by rw [monicPoly_natDegree]; exact hAj.1) hOi hOj htop
  -- the rest has positive degree: else the lift is pure, hence on-side at 0, hence
  -- the class attains at 0 — excluded by the sub-face carrier
  have hRd : 0 < R.natDegree := by
    rcases Nat.eq_zero_or_pos R.natDegree with h0 | h1
    · exfalso
      have hR1 : R = 1 := hRm.natDegree_eq_zero.mp h0
      rw [hR1, mul_one] at heq
      have hO0 : OnSide X (monicPoly a) h e' 0 := by
        have h2 := hgpure.1
        rwa [← heq] at h2
      exact hnA0 (npAttains_zero_of_onSide hπ hm0 he'0 hvis ha hO0 hsupp)
    · exact h1
  -- the type additivity
  have hty : typeOf (monicPoly a) = σ := hdec a ha
  have hdata : σ.data = (typeOf g).data + (typeOf R).data := by
    rw [← hty, heq]
    exact typeOf_mul hgm hRm
  exact ⟨g, R, hgm, hRm, heq, hgd, hRd, hgpure, hdata⟩

/-- ★★ **THE SUB-FACE LEAF INSTANCE** (LSC's discharge pointer, landed): every lift
of a sub-face leaf cell splits with additive type data — the core at the sector's
carrier. -/
theorem subface_two_block_split {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ leafSubSector O π m σ M)
    {a : Fin m → O} (ha : proj O m (M + m) a = c) :
    ∃ g R : Polynomial O, g.Monic ∧ R.Monic ∧ monicPoly a = g * R
      ∧ 0 < g.natDegree ∧ 0 < R.natDegree
      ∧ (∃ h e' : ℕ, MinFaceAt c h e' ∧ IsPure X g h e')
      ∧ σ.data = (typeOf g).data + (typeOf R).data := by
  obtain ⟨hcar, h, e', hF, hirr, hnA0⟩ := hc
  obtain ⟨⟨⟨hdec, hstr⟩, hsh⟩, hnpf⟩ := hcar
  obtain ⟨g, R, hgm, hRm, heq, hgd, hRd, hgpure, hdata⟩ :=
    two_block_split_of_not_attained_zero hπ hm0 hdec hstr hF hnA0 ha
  exact ⟨g, R, hgm, hRm, heq, hgd, hRd, ⟨h, e', hF, hgpure⟩, hdata⟩

/-- ★★ **THE TYPE-CARD FORCING** (row 3's cell-side tool): a σ-decided stratum class
whose minimal face is NOT attained at `0` forces `2 ≤ Multiset.card σ.data` — a
polygon break pins the decided type to at least two entries, at every level and
every residual genre. -/
theorem card_ge_two_of_minFace_not_attained_zero {π : O} (hπ : Irreducible π)
    {m : ℕ} (hm0 : 0 < m) {σ : FactorizationType} {K : ℕ} {c : Coeff O m K}
    (hdec : Uniformity.Density.DecidedAt O m σ K c)
    (hstr : c ∈ levelZeroStratum O m K (X ^ m))
    {h e' : ℕ} (hF : MinFaceAt c h e') (hnA0 : ¬ NPAttains c h e' 0) :
    2 ≤ Multiset.card σ.data := by
  obtain ⟨a, ha⟩ := proj_surjective O m K c
  obtain ⟨g, R, hgm, hRm, -, hgd, hRd, -, hdata⟩ :=
    two_block_split_of_not_attained_zero hπ hm0 hdec hstr hF hnA0 ha
  have h1 : 0 < Multiset.card (typeOf g).data :=
    Multiset.card_pos.mpr (typeOf_data_ne_zero hgm hgd)
  have h2 : 0 < Multiset.card (typeOf R).data :=
    Multiset.card_pos.mpr (typeOf_data_ne_zero hRm hRd)
  have hcard : Multiset.card σ.data
      = Multiset.card (typeOf g).data + Multiset.card (typeOf R).data := by
    rw [hdata, Multiset.card_add]
  omega

/-- ★ **THE SPANNING FORCING** (contrapositive census form): the minimal face of a
decided stratum class at a (sub-)singleton type ATTAINS at `0` — singleton-type
cells have full-span polygons. -/
theorem minFace_attains_zero_of_card_le_one {π : O} (hπ : Irreducible π)
    {m : ℕ} (hm0 : 0 < m) {σ : FactorizationType} {K : ℕ} {c : Coeff O m K}
    (hdec : Uniformity.Density.DecidedAt O m σ K c)
    (hstr : c ∈ levelZeroStratum O m K (X ^ m))
    (hσ : Multiset.card σ.data ≤ 1) {h e' : ℕ} (hF : MinFaceAt c h e') :
    NPAttains c h e' 0 := by
  by_contra hnA0
  have h2 := card_ge_two_of_minFace_not_attained_zero hπ hm0 hdec hstr hF hnA0
  omega

end Split

/-! ## §2 — ★★★ THE SINGLETON FIRE: the sub-face sector is EMPTY at (sub-)singleton
types, so master row 5 closes there -/

section SingletonFire

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- ★★ **THE EMPTINESS**: a sub-face leaf cell forces `Multiset.card σ.data ≥ 2`
(each of the two blocks contributes at least one type entry), so the sub-face sector
is EMPTY whenever `Multiset.card σ.data ≤ 1`. -/
theorem leafSubSector_eq_empty_of_card_le_one {π : O} (hπ : Irreducible π) {m : ℕ}
    (hm0 : 0 < m) {σ : FactorizationType} (hσ : Multiset.card σ.data ≤ 1) (M : ℕ) :
    leafSubSector O π m σ M = ∅ := by
  ext c
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hc
  obtain ⟨a, ha⟩ := proj_surjective O m (M + m) c
  obtain ⟨g, R, hgm, hRm, -, hgd, hRd, -, hdata⟩ := subface_two_block_split hπ hm0 hc ha
  have h1 : 0 < Multiset.card (typeOf g).data :=
    Multiset.card_pos.mpr (typeOf_data_ne_zero hgm hgd)
  have h2 : 0 < Multiset.card (typeOf R).data :=
    Multiset.card_pos.mpr (typeOf_data_ne_zero hRm hRd)
  have hcard : Multiset.card σ.data
      = Multiset.card (typeOf g).data + Multiset.card (typeOf R).data := by
    rw [hdata, Multiset.card_add]
  omega

end SingletonFire

/-! ### The law-level fires (`O`-free) -/

section LawFire

/-- ★★ `LeafSubfaceLaw` holds OUTRIGHT at every type with at most one entry (the
carrier is empty at every level, every complete DVR, every uniformizer). -/
theorem leafSubfaceLaw_of_card_le_one {m : ℕ} (hm0 : 0 < m) (σ : FactorizationType)
    (hσ : Multiset.card σ.data ≤ 1) : LeafSubfaceLaw m σ := by
  refine ZcURLim_zero.congr ?_
  intro O _ _ _ _ _ π hπ M
  have h1 : leafSubCount O π m σ M = 0 := by
    unfold Uniformity.Density.IFCG57.leafSubCount
    rw [leafSubSector_eq_empty_of_card_le_one hπ hm0 hσ M]
    simp
  rw [h1]
  simp

/-- ★★★ **THE SINGLETON LEAF FIRE** (LSC's pointer, landed): `LeafSectorLaw m ⟨{p}⟩`
holds UNCONDITIONALLY at every singleton type and every positive mass — the spanning
half is LSC's necklace census, the sub-face half is §2's emptiness.  Master row 5 is
CLOSED at singleton σ. -/
theorem leafSectorLaw_singleton {m : ℕ} (hm0 : 0 < m) (p : ℕ × ℕ) :
    LeafSectorLaw m ⟨{p}⟩ :=
  leafSectorLaw_of_subface hm0 _
    (leafSubfaceLaw_of_card_le_one hm0 _ (by simp))

end LawFire

/-! ## §3 — ★★★ THE PINNED TRANSPORT: the block's type is `⟨{(e', d)}⟩` exactly -/

section Pin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]

/-- `resPoly` congruence along an equality of polynomials (the `Nonempty` witness is
proof-irrelevant). -/
private theorem resPoly_congr {π : O} {u ℓ : ℕ} {f₁ f₂ : Polynomial O} (hf : f₁ = f₂)
    (hn1 : (sideSet X f₁ u ℓ).Nonempty) (hn2 : (sideSet X f₂ u ℓ).Nonempty) (H : ℕ) :
    resPoly π X f₁ u ℓ hn1 H = resPoly π X f₂ u ℓ hn2 H := by
  subst hf
  rfl

/-- `sideMin` congruence along an equality of polynomials. -/
private theorem sideMin_congr {u ℓ : ℕ} {f₁ f₂ : Polynomial O} (hf : f₁ = f₂)
    (hn1 : (sideSet X f₁ u ℓ).Nonempty) (hn2 : (sideSet X f₂ u ℓ).Nonempty) :
    sideMin X f₁ u ℓ hn1 = sideMin X f₂ u ℓ hn2 := by
  subst hf
  rfl

/-- ★★★ **THE PINNED TWO-BLOCK TRANSPORT** (the unit's star): every lift of a
sub-face leaf cell at the minimal face `(h, e')` splits as `monicPoly a = g · R` with
the block's type PINNED — `typeOf g = ⟨{(e', d)}⟩`, `g.natDegree = e' * d` for the
face's residual degree `d`, `e' * d < m` — and the class type is exactly the block
entry plus the rest: `σ.data = (e', d) ::ₘ (typeOf R).data`.

Mechanism: §1's split + B.39a §7's product laws (the `(h, e')`-sides of `g` and `R`
concatenate and their residuals multiply), so the class residual — irreducible on the
leaf sector — is `resPoly g · resPoly R`; irreducibility forces `resPoly R` to be a
unit (the block's residual has positive degree), so the rest's side degree is `0`,
the block carries the WHOLE face (`sideDeg g = d`), its residue is pinned
(`ḡ = X̄^(e'·d)` by unique factorization in `κ[X]`), and IFCG37's unconditional
`residualLeafLaw_all` reads off `typeOf g = ⟨{(e', d)}⟩`. -/
theorem subface_two_block_transport {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ leafSubSector O π m σ M) {h e' : ℕ} (hF : MinFaceAt c h e')
    {a : Fin m → O} (ha : proj O m (M + m) a = c) :
    ∃ (g R : Polynomial O) (d : ℕ), monicPoly a = g * R ∧ g.Monic ∧ R.Monic
      ∧ IsPure X g h e' ∧ 0 < d ∧ g.natDegree = e' * d ∧ e' * d < m
      ∧ typeOf g = ⟨{(e', d)}⟩ ∧ R.natDegree = m - e' * d
      ∧ σ.data = (e', d) ::ₘ (typeOf R).data := by
  -- the carrier data at the INPUT face (unique minimal face)
  obtain ⟨hcar, h₃, e₃, hF₃, hirr₃, hnA0₃⟩ := hc
  obtain ⟨hh3, he3⟩ := minFaceAt_unique hF hF₃
  subst hh3
  subst he3
  have hstr := hcar.1.1.2
  have hh1 : 1 ≤ h := hF.1
  have hhe : h < e' := hF.2.1
  have hcop : Nat.Coprime h e' := hF.2.2.1
  have hvis : NPVisibleAt c h e' := hF.2.2.2.2.2
  have he'0 : 0 < e' := by omega
  have hh0 : 0 < h := by omega
  -- §1's split, aligned to the input face by uniqueness
  obtain ⟨g, R, hgm, hRm, heq, hgd, hRd, ⟨h₂, e₂, hF₂, hgpure₂⟩, hdata⟩ :=
    subface_two_block_split hπ hm0 ⟨hcar, h, e', hF, hirr₃, hnA0₃⟩ ha
  obtain ⟨hh2, he2⟩ := minFaceAt_unique hF hF₂
  subst hh2
  subst he2
  have hgpure : IsPure X g h e' := hgpure₂
  -- the block's side data: the pure side spans `[0, deg g]`
  have hOg0 : OnSide X g h e' 0 := hgpure.1
  have hOgtop : OnSide X g h e' g.natDegree := by
    have h2 := hgpure.2
    rwa [Polynomial.natDegree_X, Nat.div_one] at h2
  have h0memg : 0 ∈ sideSet X g h e' := mem_sideSet_of_onSide (Nat.zero_le _) hOg0
  have hdmemg : g.natDegree ∈ sideSet X g h e' := mem_sideSet_of_onSide le_rfl hOgtop
  have hnf : (sideSet X g h e').Nonempty := ⟨0, h0memg⟩
  have hming : sideMin X g h e' hnf = 0 :=
    Nat.le_zero.mp (Finset.min'_le _ 0 h0memg)
  have hmaxg : sideMax X g h e' hnf = g.natDegree := by
    refine le_antisymm ?_ (Finset.le_max' _ _ hdmemg)
    refine Finset.max'_le _ _ _ ?_
    intro y hy
    have := (mem_sideSet_iff'.mp hy).1
    omega
  have htg : suppVal X g h e' ≠ ⊤ := suppVal_ne_top_of_monic hgm h e'
  -- the block's side degree `d`: `deg g = e' * d`
  have hsdg : g.natDegree = e' * sideDeg X g h e' hnf := by
    have h5 := sideMax_eq he'0 hcop htg hnf
    rwa [hmaxg, hming, zero_add] at h5
  set d := sideDeg X g h e' hnf with hd_def
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h1
    · rw [h0, Nat.mul_zero] at hsdg
      omega
    · exact h1
  -- the left heights, named
  have hHgne : npHgt X g (sideMin X g h e' hnf) ≠ ⊤ :=
    npHgt_ne_top_of_onSide he'0 htg (onSide_of_mem_sideSet (Finset.min'_mem _ hnf))
  obtain ⟨Hg, hHg⟩ := WithTop.ne_top_iff_exists.mp hHgne
  have hHg' : npHgt X g (sideMin X g h e' hnf) = ((Hg : ℕ) : ℕ∞) := hHg.symm
  have hnz : (sideSet X R h e').Nonempty := sideSet_nonempty_gen X R h e'
  have htR : suppVal X R h e' ≠ ⊤ := suppVal_ne_top_of_monic hRm h e'
  have hHRne : npHgt X R (sideMin X R h e' hnz) ≠ ⊤ :=
    npHgt_ne_top_of_onSide he'0 htR (onSide_of_mem_sideSet (Finset.min'_mem _ hnz))
  obtain ⟨HR, hHR⟩ := WithTop.ne_top_iff_exists.mp hHRne
  have hHR' : npHgt X R (sideMin X R h e' hnz) = ((HR : ℕ) : ℕ∞) := hHR.symm
  -- B.39a §7: the product's side data
  have hnfz : (sideSet X (g * R) h e').Nonempty := sideSet_nonempty_gen X (g * R) h e'
  have hminmul : sideMin X (g * R) h e' hnfz
      = sideMin X g h e' hnf + sideMin X R h e' hnz :=
    sideMin_mul_gen hπ isKey_X hh0 he'0 hcop htg htR hnf hnz hHg' hHR' hnfz
  have hsdmul : sideDeg X (g * R) h e' hnfz = d + sideDeg X R h e' hnz :=
    sideDeg_mul_gen hπ isKey_X hh0 he'0 hcop htg htR hnf hnz hHg' hHR' hnfz
  have hnpmul : npHgt X (g * R) (sideMin X g h e' hnf + sideMin X R h e' hnz)
      = ((Hg + HR : ℕ) : ℕ∞) :=
    npHgt_mul_gen hπ isKey_X hh0 he'0 hcop htg htR hnf hnz hHg' hHR'
  have hrpmul : resPoly π X (g * R) h e' hnfz (Hg + HR)
      = resPoly π X g h e' hnf Hg * resPoly π X R h e' hnz HR :=
    resPoly_mul_gen hπ isKey_X hh0 he'0 hcop htg htR hnf hnz hHg' hHR' hnfz
  -- the class residual IS the product residual (through the lift identification)
  have hseteq : sideSet X (monicPoly a) h e' = sideSet X (g * R) h e' := by rw [heq]
  have hne2 : (sideSet X (monicPoly a) h e').Nonempty := by
    rw [hseteq]
    exact hnfz
  have hmineq : sideMin X (monicPoly a) h e' hne2 = sideMin X (g * R) h e' hnfz :=
    sideMin_congr heq hne2 hnfz
  have hH2 : npHgt X (monicPoly a) (sideMin X (monicPoly a) h e' hne2)
      = ((Hg + HR : ℕ) : ℕ∞) := by
    rw [hmineq, heq, hminmul]
    exact hnpmul
  have hcrp : classResidualPoly π c h e' = resPoly π X (monicPoly a) h e' hne2 (Hg + HR) :=
    classResidualPoly_eq hπ he'0 hvis ha hne2 hH2
  have hirr' : Irreducible (resPoly π X g h e' hnf Hg * resPoly π X R h e' hnz HR) := by
    rw [← hrpmul, ← resPoly_congr heq hne2 hnfz (Hg + HR), ← hcrp]
    exact hirr₃
  -- the unit analysis: the rest's residual is a unit, the block's is THE residual
  letI : Field (resField (X : Polynomial O)) := instFieldResField isKey_X
  have hgdeg : (resPoly π X g h e' hnf Hg).natDegree = d :=
    (natDegree_resPoly hπ isKey_X he'0 hcop htg hnf hHg').1
  have hRdeg : (resPoly π X R h e' hnz HR).natDegree = sideDeg X R h e' hnz :=
    (natDegree_resPoly hπ isKey_X he'0 hcop htR hnz hHR').1
  have hnotu : ¬ IsUnit (resPoly π X g h e' hnf Hg) := by
    intro hu
    have h5 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  have huR : IsUnit (resPoly π X R h e' hnz HR) :=
    (hirr'.isUnit_or_isUnit rfl).resolve_left hnotu
  have hirrg : Irreducible (resPoly π X g h e' hnf Hg) := by
    obtain ⟨u, hu_eq⟩ := huR
    have hassoc1 : Associated (resPoly π X g h e' hnf Hg)
        (resPoly π X g h e' hnf Hg * resPoly π X R h e' hnz HR) :=
      ⟨u, by rw [hu_eq]⟩
    exact (Associated.symm hassoc1).irreducible hirr'
  -- the residue pin `ḡ = X̄^(e'·d)` (unique factorization in `κ[X]`)
  have hres : (monicPoly a).map (residue O) = X ^ m := by
    have h5 := hstr a ha
    exact h5
  have hmapmul : g.map (residue O) * R.map (residue O) = X ^ m := by
    rw [← Polynomial.map_mul, ← heq]
    exact hres
  have hdvd : g.map (residue O) ∣ (X : Polynomial (ResidueField O)) ^ m :=
    ⟨R.map (residue O), hmapmul.symm⟩
  obtain ⟨k, hkm, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X m).mp hdvd
  have heqg : g.map (residue O) = X ^ k :=
    Polynomial.eq_of_monic_of_associated (hgm.map _) (Polynomial.monic_X_pow k) hassoc
  have hk : k = g.natDegree := by
    have h5 := congrArg Polynomial.natDegree heqg
    rw [hgm.natDegree_map, Polynomial.natDegree_X_pow] at h5
    exact h5.symm
  have hgres : g.map (residue O) = X ^ (e' * d) := by
    rw [heqg, hk, hsdg]
  -- fire the unconditional leaf law: the block's type is pinned
  have htyg : typeOf g = ⟨{(e', d)}⟩ :=
    Uniformity.Density.IFCG37.residualLeafLaw_all he'0 hd0 O π hπ h hh0 hcop g hgm
      hgpure hnf rfl hgres Hg hHg' hirrg
  -- degree bookkeeping
  have hdegsum : g.natDegree + R.natDegree = m := by
    have h6 : (monicPoly a).natDegree = m := monicPoly_natDegree a
    rw [heq, Polynomial.Monic.natDegree_mul hgm hRm] at h6
    exact h6
  have he'dm : e' * d < m := by omega
  have hRdeg' : R.natDegree = m - e' * d := by omega
  -- the pinned data decomposition
  have hdata' : σ.data = (e', d) ::ₘ (typeOf R).data := by
    rw [hdata, htyg]
    exact Multiset.singleton_add _ _
  exact ⟨g, R, d, heq, hgm, hRm, hgpure, hd0, hsdg, he'dm, htyg, hRdeg', hdata'⟩

/-- ★ **The face's block type is an ENTRY of the class type**: a sub-face leaf cell
at minimal face `(h, e')` forces `(e', d) ∈ σ.data` for the face's residual degree
`d`, with `0 < d` and `e' * d < m`.  (The census consumer's form.) -/
theorem face_block_mem_type {π : O} (hπ : Irreducible π) {m : ℕ} (hm0 : 0 < m)
    {σ : FactorizationType} {M : ℕ} {c : Coeff O m (M + m)}
    (hc : c ∈ leafSubSector O π m σ M) {h e' : ℕ} (hF : MinFaceAt c h e') :
    ∃ d : ℕ, 0 < d ∧ e' * d < m ∧ (e', d) ∈ σ.data := by
  obtain ⟨a, ha⟩ := proj_surjective O m (M + m) c
  obtain ⟨g, R, d, -, -, -, -, hd0, -, hdm, -, -, hdata⟩ :=
    subface_two_block_transport hπ hm0 hc hF ha
  refine ⟨d, hd0, hdm, ?_⟩
  rw [hdata]
  exact Multiset.mem_cons_self _ _

end Pin

/-! ## §4 — ★★★ THE MASTERS RECOMPUTED: the leaf row weakens to NON-SINGLETON σ

Both landed spines consumed row 5 at every guarded `(e, σ)`.  §2 closes the
singleton types outright, so the surviving premise adds `2 ≤ Multiset.card σ.data`
to the guards — strictly weaker, and the exact honest remainder (a sub-face leaf
cell FORCES at least two type entries, so no content is lost). -/

section Masters

open Uniformity.Density.IFCG38 (SplitConvolutionDefectLaw)
open Uniformity.Density.IFCG44 (PowerConvolutionDefectLaw PowerFullSpanLaw)
open Uniformity.Density.IFCG48 (FactorCorrespondenceAt)
open Uniformity.Density.IFCG51 (EisFullSpanRemainderLaw)
open Uniformity.Density.IFCG58 (VisCensusLaw)

/-- The leaf row's supply: `LeafSectorLaw` from the non-singleton sub-face premise
(the singleton case is §2's unconditional fire). -/
private theorem leafSectorLaw_of_nonsingleton_subface {e : ℕ} (he : 5 ≤ e)
    (σ : FactorizationType)
    (hsub : 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ) : LeafSectorLaw e σ := by
  refine leafSectorLaw_of_subface (by omega : 0 < e) σ ?_
  by_cases hcard : 2 ≤ Multiset.card σ.data
  · exact hsub hcard
  · exact leafSubfaceLaw_of_card_le_one (by omega : 0 < e) σ (by omega)

/-- ★★★ **THE CENSUS MASTER ON PCD's SPINE, LEAF ROW RECOMPUTED**: the all-degree
decided slice rests on {`∀ g, VisCensusLaw g`, `PowerFullSpanLaw`,
`LeafSubfaceLaw` at NON-SINGLETON σ only, the `e = 4` remainder laws} —
IFCG58's `decidedSliceAt_all_of_visCensus` with the leaf premise guarded by
`2 ≤ Multiset.card σ.data`. -/
theorem decidedSliceAt_all_of_visCensus'
    (hVC : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → ∀ g, VisCensusLaw g e σ)
    (hPF : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → PowerFullSpanLaw e σ)
    (hLeafSub : ∀ e : ℕ, 5 ≤ e →
      (∀ k, k < e → ∀ σ' : FactorizationType, σ'.degree = k → DecidedValueLaw k σ') →
      ∀ σ : FactorizationType, σ.degree = e → Witnessed e σ →
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ)
    (hR4 : ∀ σ : FactorizationType, σ.degree = 4 → Witnessed 4 σ →
      (∃ p ∈ σ.data, 2 ∣ p.1) → ConeRemainderLaw 4 σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG58.decidedSliceAt_all_of_visCensus hVC hPF
    (fun e he hsm σ hσ hwit hram =>
      leafSectorLaw_of_nonsingleton_subface he σ (hLeafSub e he hsm σ hσ hwit hram))
    hR4

/-- ★★★ **THE CENSUS MASTER ON LSC's SPINE, LEAF ROW RECOMPUTED**: IFCG57's
`decidedSliceAt_all_of_MASTER'` with the `LeafSubfaceLaw` premise guarded by
`2 ≤ Multiset.card σ.data`. -/
theorem decidedSliceAt_all_of_MASTER''
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
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ) :
    ∀ n : ℕ, Uniformity.Density.DecidedSliceAt n :=
  Uniformity.Density.IFCG55.decidedSliceAt_all_of_MASTER hFC hEis hSD hPD
    (fun e he hsm σ hσ hwit hram =>
      leafSectorLaw_of_nonsingleton_subface he σ (hLeafSub e he hsm σ hσ hwit hram))

universe uW uG uKt uL

/-- ★★★ **THE CAPSTONE MASTER, LEAF ROW RECOMPUTED**: IFCG57's
`capstoneHypotheses_of_MASTER'` with the `LeafSubfaceLaw` premise guarded by
`2 ≤ Multiset.card σ.data` (ID12's honesty frame applies verbatim). -/
theorem capstoneHypotheses_of_MASTER'' (n : ℕ)
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
        (∃ p ∈ σ.data, p.1 ≠ 1) → 2 ≤ Multiset.card σ.data → LeafSubfaceLaw e σ) :
    CapstoneHypotheses.{uW, uG, uKt, uL} n :=
  Uniformity.Density.IFCG57.capstoneHypotheses_of_MASTER' n hladder hdeepTwist hFC
    hEis hSD hPD
    (fun e he hsm σ hσ hwit hram => by
      by_cases hcard : 2 ≤ Multiset.card σ.data
      · exact hLeafSub e he hsm σ hσ hwit hram hcard
      · exact leafSubfaceLaw_of_card_le_one (by omega : 0 < e) σ (by omega))

end Masters

end Uniformity.Density.IFCG59

end

/-! ## AXCHECK FOOTER — §0's bridge is pure Lean core `{propext, Classical.choice,
Quot.sound}`; §§1–3 and the two census masters expect Lean core PLUS exactly the
owner-signed gate-(b) cite `Uniformity.Density.Leaf.exists_slope_factorization`
(B.42, inherited through IFCG26 §2 / IFCG35 / IFCG37 / the spines — never
re-consumed); the capstone master additionally inherits exactly
`agnprw_termination` (ID12, previously declared).  The C.33 cites and
`AX_cellRecursion` must NOT occur. -/

#print axioms Uniformity.Density.IFCG59.npAttains_zero_of_onSide
#print axioms Uniformity.Density.IFCG59.two_block_split_of_not_attained_zero
#print axioms Uniformity.Density.IFCG59.subface_two_block_split
#print axioms Uniformity.Density.IFCG59.card_ge_two_of_minFace_not_attained_zero
#print axioms Uniformity.Density.IFCG59.minFace_attains_zero_of_card_le_one
#print axioms Uniformity.Density.IFCG59.leafSubSector_eq_empty_of_card_le_one
#print axioms Uniformity.Density.IFCG59.leafSubfaceLaw_of_card_le_one
#print axioms Uniformity.Density.IFCG59.leafSectorLaw_singleton
#print axioms Uniformity.Density.IFCG59.subface_two_block_transport
#print axioms Uniformity.Density.IFCG59.face_block_mem_type
#print axioms Uniformity.Density.IFCG59.decidedSliceAt_all_of_visCensus'
#print axioms Uniformity.Density.IFCG59.decidedSliceAt_all_of_MASTER''
#print axioms Uniformity.Density.IFCG59.capstoneHypotheses_of_MASTER''
